import Lean
import Lean.Data.Json
import Lean.Data.Json.FromToJson
import Lean.Elab.Frontend
import Lean.Elab.Tactic
import Lean.Elab.Import
import Lean.Meta

namespace Goudlokje

open Lean Elab Meta

/-- A position in a source file where a probe tactic succeeded. -/
structure ProbeResult where
  file        : String
  line        : Nat
  column      : Nat
  exercise    : String
  lineInProof : Nat
  tactic      : String
  deriving Repr, BEq, Inhabited, ToJson, FromJson

/-- Scan backwards in `input` from `proofStartLine` (1-based) for a Verbose
    `Exercise "…"` or `Example "…"` declaration and return the quoted name.
    Falls back to "example" if none is found within 30 lines or if a
    new declaration boundary (theorem/lemma/def/…) is encountered first. -/
private def findExerciseName (input : String) (proofStartLine : Nat) : String :=
  let lines := (input.splitOn "\n").toArray
  let upper := min proofStartLine lines.size
  let lower := if upper > 30 then upper - 30 else 0
  let range := (List.range (upper - lower)).map (fun k => upper - 1 - k)
  let stopPrefixes : List String :=
    ["theorem ", "lemma ", "def ", "noncomputable ", "example ", "abbrev "]
  let (result, _) := range.foldl (fun (name, stop) idx =>
    if stop then (name, stop)
    else
      let line := (lines[idx]? |>.getD "").trimAscii.toString
      if stopPrefixes.any (fun p => line.startsWith p) then ("example", true)
      else if line.startsWith "Exercise \"" || line.startsWith "Example \"" then
        let after : String :=
          if line.startsWith "Exercise \"" then (line.drop "Exercise \"".length).toString
          else (line.drop "Example \"".length).toString
        match after.splitOn "\"" with
        | name :: _ => (name, true)
        | []        => ("example", true)
      else (name, false))
    ("example", false)
  result

/-- Return true if this `TacticInfo` is a synthetic container or proof-scaffolding
    tactic that does not correspond to a user-written proof step.

    Several sources generate such nodes:

    1. **The `by` block itself** (`Lean.Parser.Term.byTactic`): Lean's term
       elaborator calls `withTacticInfoContext` on the `by` expression, producing
       a `TacticInfo` whose `goalsBefore` equals the theorem's initial goal.
       A probe tactic that closes that goal would appear here — but the student
       must write *some* proof regardless, so this is never a real shortcut.

    2. **Tactic sequence containers** (`Lean.Parser.Tactic.tacticSeq`,
       `Lean.Parser.Tactic.tacticSeq1Indented`): wrapper nodes that span an
       entire tactic block; the individual child tactics already produce their
       own `TacticInfo` nodes.

    3. **Lean Verbose `Exercise`/`Example` proof wrappers**
       (`Verbose.English.withSuggestions`, `Verbose.French.withSuggestions`,
       `withoutSuggestions`): `mkExercise` expands to
       `example … := by with(out)_suggestions%$tkp <proof>; done`
       where `tkp` is the `Proof:` token.  The `%$tkp` annotation gives the
       wrapper tactic a source position pointing at `Proof:` and `goalsBefore`
       equal to the exercise conclusion, making it indistinguishable from the
       first proof step without this filter.

    4. **The `·` focused-proof bullet** (`Lean.cdotTk`, `Lean.cdot`): the `·` syntax
       produces two `TacticInfo` nodes at the bullet position — `Lean.cdotTk` for the
       token and `Lean.cdot` for the tactic evaluator it expands into.  Both have
       `goalsBefore` equal to the focused subgoal.  This is proof scaffolding — the
       student must write something inside the bullet regardless.

    5. **Verbose `strg_assumption`** (`tacticStrg_assumption`): the Verbose tactic
       `We conclude by hypothesis` elaborates into an internal `strg_assumption` call.
       This generates a child `TacticInfo` node at a position inside the tactic text,
       not a position where a student could insert a different tactic.  Treating it as
       a probe position produces false positives when the probe tactic is `assumption`
       or equivalent (the student is already using assumption via the Verbose syntax).

    Kind names discovered empirically:
    - `Lean.Parser.Term.byTactic` — Lean core `by` block (as a term)
    - `by`                         — `by` as a tactic-level syntax node
    - `Lean.Parser.Tactic.tacticSeq` / `tacticSeq1Indented` — sequence containers
    - `Verbose.English.withSuggestions` — Verbose/English/Widget.lean
    - `Verbose.French.withSuggestions`  — Verbose/French/Widget.lean
    - `withoutSuggestions`              — Verbose/Tactics/Statements.lean
    - `Lean.cdotTk`                     — `·` bullet token node
    - `Lean.cdot`                       — `·` bullet tactic evaluator node
    - `tacticStrg_assumption`           — internal Verbose `strg_assumption` call -/
private def isSyntheticTacticContainer (ti : TacticInfo) : Bool :=
  let k := ti.stx.getKind.toString
  k == "Lean.Parser.Term.byTactic"                ||
  k == "by"                                       ||
  k == "Lean.Parser.Tactic.tacticSeq"             ||
  k == "Lean.Parser.Tactic.tacticSeq1Indented"    ||
  k == "Verbose.English.withSuggestions"           ||
  k == "Verbose.French.withSuggestions"            ||
  k == "withoutSuggestions"                        ||
  k == "Lean.cdotTk"                              ||
  k == "Lean.cdot"                                ||
  k == "tacticStrg_assumption"

/-- Return true if this `TacticInfo` node is an opaque Verbose tactic whose children
    are internal elaboration artifacts and must not be traversed.

    `tacticLet'sProveThat_` (unqualified, used for nested "Let's prove that …"),
    `tacticLet'sProveThat_Works_` (for existential witness steps, "Let's prove that N works"),
    and `tacticWeCompute_` all expand into internal elaboration nodes (`first`, `apply`,
    `refine`, `show`, `done`, `«;»`, `tacticCheck_suitable`, `eqRefl`, etc.) that share
    the same source position. Descending into them produces false-positive probe positions.

    These nodes are collected themselves (as step-boundary markers or user-visible
    tactics for `applyVerboseStepFilter`) but their children are not recursed into.
    See `collectTacticInfos` for the push-but-no-recurse handling. -/
private def isVerboseOpaqueSubtree (ti : TacticInfo) : Bool :=
  let k := ti.stx.getKind.toString
  k == "tacticLet'sProveThat_" ||
  k == "tacticLet'sProveThat_Works_" ||
  k == "tacticWeCompute_"

/-- Collect (ContextInfo, TacticInfo) pairs from an InfoTree.
    We use `PartialContextInfo.mergeIntoOuter?` to resolve the full `ContextInfo`.
    Synthetic container nodes (`by` blocks, tactic sequences, Verbose proof wrappers)
    are excluded via `isSyntheticTacticContainer`.
    Opaque Verbose subtrees (`tacticLet'sProveThat_`) are pruned entirely via
    `isVerboseOpaqueSubtree`. -/
private partial def collectTacticInfos
    (ci? : Option ContextInfo) (tree : InfoTree)
    (acc : Array (ContextInfo × TacticInfo)) : Array (ContextInfo × TacticInfo) :=
  match tree with
  | .context pci child =>
    let newCi? := pci.mergeIntoOuter? ci?
    collectTacticInfos newCi? child acc
  | .node info children =>
    match ci?, info with
    | some ci, .ofTacticInfo ti =>
      if isVerboseOpaqueSubtree ti then
        -- Push the node itself (it is a step boundary for applyVerboseStepFilter)
        -- but do NOT recurse into children (they are internal elaboration artifacts).
        if !ti.goalsBefore.isEmpty then acc.push (ci, ti) else acc
      else
        let acc' := if !ti.goalsBefore.isEmpty && !isSyntheticTacticContainer ti
                    then acc.push (ci, ti) else acc
        children.foldl (fun a c => collectTacticInfos ci? c a) acc'
    | _, _ =>
      children.foldl (fun a c => collectTacticInfos ci? c a) acc
  | .hole _ => acc

/-- Try running `tacticStr` in the goal state captured by `ti`, using context `ci`.
    Returns `true` if the tactic closes the first goal. -/
private def tryTacticAt
    (ci : ContextInfo) (mctxBefore : MetavarContext)
    (goal : MVarId) (tacticStr : String) : IO Bool := do
  match Parser.runParserCategory ci.env `tactic tacticStr with
  | .error _ => return false
  | .ok stx =>
    try
      let lctx : LocalContext :=
        (mctxBefore.decls.find? goal).map (·.lctx) |>.getD {}
      ci.runMetaM lctx do
        withMCtx mctxBefore do
          let (goals, _) ← Term.TermElabM.run
            (ctx := { declName? := ci.parentDecl? }) <|
            Tactic.run goal (Tactic.evalTactic stx)
          return goals.isEmpty
    catch _ => return false

/-- Process commands one at a time, accumulating info trees from each command.
    `elabCommandTopLevel` resets `infoState.trees` at the start of each command,
    so we must collect per-command trees before the next command overwrites them. -/
partial def processCommandsCollectTrees
    (ctx : Frontend.Context)
    (state : Frontend.State)
    (acc : Array InfoTree) : IO (Array InfoTree × Frontend.State) := do
  let (isDone, newState) ← (Frontend.processCommand.run ctx).run state
  let cmdTrees := newState.commandState.infoState.trees.toArray
  let newAcc := acc ++ cmdTrees
  if isDone then
    return (newAcc, newState)
  else
    processCommandsCollectTrees ctx newState newAcc

/-- Return true if the tactic syntax kind belongs to the Lean Verbose library.
    Covers step-boundary tactics, proof wrappers, and other Verbose-specific kinds.
    Used to determine whether an InfoTree originates from a Verbose Lean proof. -/
def isVerboseTacticKind (kind : String) : Bool :=
  kind == "tacticLet'sFirstProveThat_"                             ||
  kind == "tacticLet'sNowProveThat_"                              ||
  kind == "tacticLet'sProveThat_Works_"                           ||
  kind == "tacticLet'sProveThat_"                                 ||
  kind == "Verbose.NameLess.tacticAssumeThat__"                   ||
  kind == "Verbose.English.tacticWeDiscussDependingOnWhether_Or_" ||
  kind == "tacticWeCompute_"                                      ||
  kind == "Verbose.English.withSuggestions"                       ||
  kind == "Verbose.French.withSuggestions"                        ||
  kind == "withoutSuggestions"                                    ||
  kind == "tacticStrg_assumption"

/-- Return true if `tree` contains at least one Verbose tactic node.
    Used to restrict shortcut detection and lint checks to Verbose Lean proofs only. -/
partial def treeContainsVerbose (tree : InfoTree) : Bool :=
  match tree with
  | .context _ child => treeContainsVerbose child
  | .node info children =>
    (match info with
     | .ofTacticInfo ti => isVerboseTacticKind ti.stx.getKind.toString
     | _ => false) ||
    children.any treeContainsVerbose
  | .hole _ => false

/-- Return true if the tactic is a Lean Verbose step-boundary tactic.
    These tactics introduce a new sub-goal (the "step goal") in a Verbose proof.
    Kind names discovered empirically by inspecting the Verbose English library. -/
private def isVerboseStepBoundary (ti : TacticInfo) : Bool :=
  let k := ti.stx.getKind.toString
  k == "tacticLet'sFirstProveThat_"                              ||
  k == "tacticLet'sNowProveThat_"                               ||
  k == "tacticLet'sProveThat_Works_"                            ||
  k == "tacticLet'sProveThat_"                                  ||
  k == "Verbose.NameLess.tacticAssumeThat__"                    ||
  k == "Verbose.English.tacticWeDiscussDependingOnWhether_Or_"

/-- When `filterVerboseSteps` is true, filter tactic positions from declarations that
    contain Verbose step boundaries (e.g. `Let's first prove that …`).

    For each such declaration, apply per-step skip-last: keep only the first
    non-boundary tactic if the step has ≥2 such tactics; skip the step entirely if it
    has exactly one (the student must write that tactic regardless — not a shortcut).

    Declarations WITHOUT step boundaries are returned unchanged; the caller is expected
    to call `skipLastPerDeclaration` afterwards to handle the declaration-level skip for
    those groups (and also to handle per-tree splits in Waterproof/Verso `#doc` files,
    where each step body may appear in its own InfoTree with no visible boundary).

    Filtering is applied per-declaration (grouped by `parentDecl?`) so that filter
    state does not leak across independent theorems and exercises. -/
private def applyVerboseStepFilter
    (infos : Array (ContextInfo × TacticInfo)) (fileMap : FileMap) :
    Array (ContextInfo × TacticInfo) :=
  -- Early exit: no step boundaries present → no filtering needed; caller handles skip-last
  if !infos.any (fun (_, ti) => isVerboseStepBoundary ti) then infos
  else
    -- Sort by source position
    let withPos := infos.map fun (ci, ti) =>
      (fileMap.toPosition (ti.stx.getPos?.getD 0), ci, ti)
    let sorted := withPos.toList.mergeSort (fun (p1, _, _) (p2, _, _) =>
      p1.line < p2.line || (p1.line == p2.line && p1.column < p2.column))
    -- Group consecutive tactics by enclosing declaration (parentDecl?).
    -- foldl accumulates groups in reverse with items within each group also reversed;
    -- we reverse both at the end to restore source order.
    let groups : List (Option Name × List (ContextInfo × TacticInfo)) :=
      sorted.foldl (fun acc (_, ci, ti) =>
        let decl := ci.parentDecl?
        match acc with
        | [] => [(decl, [(ci, ti)])]
        | (d, items) :: rest =>
          if d == decl then (d, (ci, ti) :: items) :: rest
          else (decl, [(ci, ti)]) :: acc)
        []
    -- Per-step skip-last: partition `items` (source order) into steps delimited by
    -- step-boundary tactics, then for each step keep the first non-boundary tactic
    -- only when the step contains ≥2 non-boundary tactics.  Single-tactic steps are
    -- skipped: the student must write that one tactic regardless.
    let filterStepBoundaryGroup (items : List (ContextInfo × TacticInfo)) :
        List (ContextInfo × TacticInfo) :=
      -- Build steps: each boundary flushes the current step into stepsRev.
      -- Items within each step are accumulated in reverse for efficiency.
      let (stepsRev, currentStepRev) := items.foldl
        (fun (stepsRev, currentStepRev) (ci, ti) =>
          if isVerboseStepBoundary ti then
            (if currentStepRev.isEmpty then stepsRev
             else currentStepRev.reverse :: stepsRev,
             [])
          else
            (stepsRev, (ci, ti) :: currentStepRev))
        ([], [])
      let allSteps :=
        (if currentStepRev.isEmpty then stepsRev
         else currentStepRev.reverse :: stepsRev).reverse
      -- Keep the first tactic of each step that has ≥2 tactics; skip single-tactic steps.
      allSteps.foldl (fun acc step =>
        match step with
        | [] | [_] => acc
        | first :: _ => acc ++ [first]) []
    -- For each group: if it has step boundaries apply per-step skip-last,
    -- otherwise return unchanged (skipLastPerDeclaration in the caller handles it).
    let filterGroup (items : List (ContextInfo × TacticInfo)) :
        List (ContextInfo × TacticInfo) :=
      if !items.any (fun (_, ti) => isVerboseStepBoundary ti) then
        items
      else
        filterStepBoundaryGroup items
    -- Reverse groups and items to restore source order, apply filter to each group
    let allResults : List (ContextInfo × TacticInfo) :=
      groups.reverse.foldl (fun acc (_, items) => acc ++ filterGroup items.reverse) []
    allResults.toArray

/-- For each declaration in `infos`, drop the last tactic position (by source order).
    A shortcut at the final step of a proof never saves proof lines — the student
    must still write that step (or an equivalent).  Skipping it avoids false positives
    where a probe tactic can close the goal at the last line of an exercise.

    Grouping follows the same consecutive-`parentDecl?` logic as `applyVerboseStepFilter`:
    tactics are grouped by consecutive runs sharing the same `parentDecl?` so that
    anonymous `example` blocks, which share `parentDecl? = none`, are correctly
    separated when each is processed in its own InfoTree. -/
private def skipLastPerDeclaration
    (infos : Array (ContextInfo × TacticInfo)) (fileMap : FileMap) :
    Array (ContextInfo × TacticInfo) :=
  let withPos := infos.map fun (ci, ti) =>
    (fileMap.toPosition (ti.stx.getPos?.getD 0), ci, ti)
  let sorted := withPos.toList.mergeSort (fun (p1, _, _) (p2, _, _) =>
    p1.line < p2.line || (p1.line == p2.line && p1.column < p2.column))
  let groups : List (Option Name × List (ContextInfo × TacticInfo)) :=
    sorted.foldl (fun acc (_, ci, ti) =>
      let decl := ci.parentDecl?
      match acc with
      | [] => [(decl, [(ci, ti)])]
      | (d, items) :: rest =>
        if d == decl then (d, (ci, ti) :: items) :: rest
        else (decl, [(ci, ti)]) :: acc)
      []
  -- groups is in reverse source order; items within each group are also reversed.
  -- Restore source order and drop the last tactic of each group.
  let allResults :=
    groups.reverse.foldl (fun acc (_, items) =>
      acc ++ items.reverse.dropLast)
      []
  allResults.toArray

/-- Collect all unique syntax kind names from TacticInfo nodes in a file.
    Useful for debugging and discovering kind names for Verbose/Waterproof tactics. -/
def collectTacticKinds (filePath : System.FilePath) : IO (Array String) := do
  Lean.initSearchPath (← Lean.findSysroot)
  unsafe Lean.enableInitializersExecution
  let input ← IO.FS.readFile filePath
  let opts  := Elab.async.set Options.empty false
  let inputCtx := Parser.mkInputContext input filePath.toString
  let (header, parserState, _messages) ← Parser.parseHeader inputCtx
  let (env, _msgs) ← processHeader header opts {} inputCtx
  let initCmdState : Command.State := Command.mkState env {} opts
  let initState : Frontend.State := {
    commandState := initCmdState
    parserState  := parserState
    cmdPos       := 0
  }
  let ctx : Frontend.Context := { inputCtx }
  let (allTrees, finalState) ← processCommandsCollectTrees ctx initState #[]
  let assignment := finalState.commandState.infoState.assignment
  let resolvedTrees := allTrees.map fun t => t.substitute assignment
  let tacticInfos : Array (ContextInfo × TacticInfo) :=
    resolvedTrees.foldl (fun acc t => collectTacticInfos none t acc) #[]
  let kinds := tacticInfos.foldl (fun acc (_, ti) =>
    let k := ti.stx.getKind.toString
    if acc.contains k then acc else acc.push k) #[]
  return kinds

/-- Collect (kind, line, column) for every TacticInfo node that survives
    `isSyntheticTacticContainer` filtering.  Useful for diagnosing which nodes are
    at a specific source position after filter changes. -/
def collectTacticKindsWithPositions (filePath : System.FilePath) :
    IO (Array (String × Nat × Nat)) := do
  Lean.initSearchPath (← Lean.findSysroot)
  unsafe Lean.enableInitializersExecution
  let input ← IO.FS.readFile filePath
  let opts  := Elab.async.set Options.empty false
  let inputCtx := Parser.mkInputContext input filePath.toString
  let (header, parserState, _messages) ← Parser.parseHeader inputCtx
  let (env, _msgs) ← processHeader header opts {} inputCtx
  let initCmdState : Command.State := Command.mkState env {} opts
  let initState : Frontend.State := {
    commandState := initCmdState
    parserState  := parserState
    cmdPos       := 0
  }
  let ctx : Frontend.Context := { inputCtx }
  let (allTrees, finalState) ← processCommandsCollectTrees ctx initState #[]
  let assignment := finalState.commandState.infoState.assignment
  let resolvedTrees := allTrees.map fun t => t.substitute assignment
  let tacticInfos : Array (ContextInfo × TacticInfo) :=
    resolvedTrees.foldl (fun acc t => collectTacticInfos none t acc) #[]
  return tacticInfos.map fun (ci, ti) =>
    let pos := ci.fileMap.toPosition (ti.stx.getPos?.getD 0)
    (ti.stx.getKind.toString, pos.line, pos.column)

inductive TacticKindCategory where
  | synthetic    -- filtered by isSyntheticTacticContainer; internal elaboration artifact
  | boundary     -- filtered by isVerboseStepBoundary; delimits a Verbose proof step
  | opaque       -- filtered by isVerboseOpaqueSubtree; subtree pruned entirely
  | opaqueChild  -- only reachable inside an opaque subtree; never collected in practice
  | userTactic   -- real Verbose tactic written by the student; valid probe target
  | unknown      -- not yet classified; may need attention
  deriving Repr, BEq

/-- Classify every distinct tactic syntax kind found in `filePath` according to
    how `collectTacticInfos` / `applyVerboseStepFilter` currently treats it.
    Returns one entry per unique kind, sorted alphabetically.

    Intended as a permanent debug utility: run it on a fixture file to check
    whether all Verbose tactics are correctly classified.  Any `unknown` entry
    is a candidate for `isSyntheticTacticContainer`, `isVerboseStepBoundary`, or
    `isVerboseOpaqueSubtree`. -/
private partial def collectAllTacticInfos
    (ci? : Option ContextInfo) (tree : InfoTree)
    (acc : Array (ContextInfo × TacticInfo)) : Array (ContextInfo × TacticInfo) :=
  match tree with
  | .context pci child =>
    collectAllTacticInfos (pci.mergeIntoOuter? ci?) child acc
  | .node info children =>
    let acc' := match ci?, info with
      | some ci, .ofTacticInfo ti =>
        if !ti.goalsBefore.isEmpty then acc.push (ci, ti) else acc
      | _, _ => acc
    children.foldl (fun a c => collectAllTacticInfos ci? c a) acc'
  | .hole _ => acc

def classifyTacticKinds (filePath : System.FilePath) :
    IO (Array (String × TacticKindCategory)) := do
  Lean.initSearchPath (← Lean.findSysroot)
  unsafe Lean.enableInitializersExecution
  let input ← IO.FS.readFile filePath
  let opts  := Elab.async.set Options.empty false
  let inputCtx := Parser.mkInputContext input filePath.toString
  let (header, parserState, _messages) ← Parser.parseHeader inputCtx
  let (env, _msgs) ← processHeader header opts {} inputCtx
  let initCmdState : Command.State := Command.mkState env {} opts
  let initState : Frontend.State := {
    commandState := initCmdState
    parserState  := parserState
    cmdPos       := 0
  }
  let ctx : Frontend.Context := { inputCtx }
  -- Collect ALL tactic nodes before any filtering, using a raw traversal
  -- so we can see what each filter would classify.
  let (allTrees, finalState) ← processCommandsCollectTrees ctx initState #[]
  let assignment := finalState.commandState.infoState.assignment
  let resolvedTrees := allTrees.map fun t => t.substitute assignment
  -- Raw collection: bypass isSyntheticTacticContainer and isVerboseOpaqueSubtree
  -- so we see every node, not just the surviving ones.
  let allInfos : Array (ContextInfo × TacticInfo) :=
    resolvedTrees.foldl (fun acc t => collectAllTacticInfos none t acc) #[]
  -- Build a deduplicated kind → category map
  let categorize (k : String) : TacticKindCategory :=
    if k == "Lean.Parser.Term.byTactic"             ||
       k == "by"                                     ||
       k == "Lean.Parser.Tactic.tacticSeq"           ||
       k == "Lean.Parser.Tactic.tacticSeq1Indented"  ||
       k == "Verbose.English.withSuggestions"         ||
       k == "Verbose.French.withSuggestions"          ||
       k == "withoutSuggestions"                      ||
       k == "Lean.cdotTk"                            ||
       k == "Lean.cdot"                              ||
       k == "tacticStrg_assumption"
    then .synthetic
        else if k == "tacticLet'sFirstProveThat_"                             ||
            k == "tacticLet'sNowProveThat_"                               ||
            k == "tacticLet'sProveThat_Works_"                            ||
            k == "tacticLet'sProveThat_"                                  ||
            k == "Verbose.NameLess.tacticAssumeThat__"                    ||
            k == "Verbose.English.tacticWeDiscussDependingOnWhether_Or_"
    then .boundary
        else if k == "tacticWeCompute_"
        then .opaque
    -- Children of opaque subtrees: only reachable via collectAllTacticInfos
    -- (which bypasses opaque pruning).  Never collected in real operation.
    else if k == "Lean.Parser.Tactic.apply"         ||
            k == "Lean.Parser.Tactic.done"           ||
            k == "Lean.Parser.Tactic.eqRefl"         ||
            k == "Lean.Parser.Tactic.first"          ||
            k == "Lean.Parser.Tactic.focus"          ||
            k == "Lean.Parser.Tactic.paren"          ||
            k == "Lean.Parser.Tactic.refine"         ||
            k == "Lean.Parser.Tactic.seq1"           ||
            k == "Lean.Parser.Tactic.show"           ||
            k == "Lean.Parser.Tactic.tacticIterate____" ||
            k == "Lean.Parser.Tactic.tacticRfl"      ||
            k == "Lean.Parser.Tactic.tacticTry_"     ||
            k == "focus"                             ||
            k == "tacticCheck_suitable"              ||
            k == "«;»"
    then .opaqueChild
    -- Real Verbose tactics written by students; valid probe targets
        else if k == "tacticWeConcludeBy_"                        ||
            k == "Verbose.English.tacticSince_WeConcludeThat_" ||
            k == "Verbose.English.tacticSince_WeGetThat_Hence_"
    then .userTactic
    else .unknown
  let kindMap := allInfos.foldl (fun acc (_, ti) =>
    let k := ti.stx.getKind.toString
    if acc.any (fun (k', _) => k' == k) then acc
    else acc.push (k, categorize k)) #[]
  -- Sort alphabetically by kind name
  let sorted := kindMap.toList.mergeSort (fun (a, _) (b, _) => a < b)
  return sorted.toArray

/-- Keep only lines that are meaningful Lean context outside fenced `lean` blocks.
    This is used as a fallback for Verso/Waterproof `#doc` sources where the
    fenced code is no longer elaborated as ordinary top-level commands. -/
private def keepOutsideLeanFenceLine (line : String) : Bool :=
  let trimmed := line.trimAscii.toString
  trimmed.isEmpty ||
  trimmed.startsWith "--" ||
  trimmed.startsWith "/-" ||
  trimmed.startsWith "-/" ||
  trimmed.startsWith "import " ||
  trimmed.startsWith "open " ||
  trimmed.startsWith "namespace " ||
  trimmed.startsWith "section " ||
  trimmed.startsWith "end " ||
  trimmed.startsWith "set_option "

/-- Build an overlay source that preserves imports/preamble outside fenced blocks
    and keeps only the contents of fenced `lean` blocks. All other lines are
    replaced by blanks so source positions still line up with the original file. -/
private def extractLeanFenceOverlay? (input : String) : Option String :=
  let (linesRev, _inFence, sawFence, keptLean) :=
    (input.splitOn "\n").foldl
      (fun (acc : List String × Bool × Bool × Bool) line =>
        let (linesRev, inFence, sawFence, keptLean) := acc
        let trimmed := line.trimAscii.toString
        if inFence then
          if trimmed == "```" then
            ("" :: linesRev, false, sawFence, keptLean)
          else
            (line :: linesRev, true, sawFence, keptLean || !trimmed.isEmpty)
        else if trimmed.startsWith "```lean" then
          ("" :: linesRev, true, true, keptLean)
        else
          let kept := if keepOutsideLeanFenceLine line then line else ""
          (kept :: linesRev, false, sawFence, keptLean))
      ([], false, false, false)
  if sawFence && keptLean then
    some ("\n".intercalate linesRev.reverse)
  else
    none

/-- Analyse a single Lean input string, returning every (position, tactic) pair
    where a probe tactic succeeds.
    `originalSource`, when provided, is used by `findExerciseName` to recover
    Verbose exercise names from lines that may have been blanked in `input`
    (e.g. when `input` is a fence-overlay from `extractLeanFenceOverlay?`). -/
private def analyzeInput
    (displayPath : System.FilePath) (input : String) (probeTactics : Array String)
    (filterVerboseSteps : Bool := false)
    (onProbe : Option (Nat → Nat → String → Bool → IO Unit) := none)
    (originalSource : Option String := none) :
    IO (Array ProbeResult) := do
  let opts  := Elab.async.set Options.empty false
  let inputCtx := Parser.mkInputContext input displayPath.toString
  let (header, parserState, _messages) ← Parser.parseHeader inputCtx
  let (env, _) ← processHeader header opts {} inputCtx
  let initCmdState : Command.State := Command.mkState env {} opts
  let initState : Frontend.State := {
    commandState := initCmdState
    parserState  := parserState
    cmdPos       := 0
  }
  let ctx : Frontend.Context := { inputCtx }
  let sourceForNames := originalSource.getD input
  let mut results : Array ProbeResult := #[]
  let mut state := initState
  let mut done := false
  let mut cmdIdx := 0
  while !done do
    let (isDone, newState) ← (Frontend.processCommand.run ctx).run state
    -- Consume each command's trees immediately to avoid retaining all frontend data.
    let assignment := newState.commandState.infoState.assignment
    let resolvedTrees := newState.commandState.infoState.trees.toArray.map fun t =>
      t.substitute assignment
    -- Collect raw tactic infos from ALL trees of this command before filtering.
    -- A single Verbose Exercise command can produce multiple InfoTree nodes where
    -- step-boundary tactics (e.g. `tacticLet'sFirstProveThat_`) and their body
    -- tactics (e.g. `tacticWeCompute_`) land in different trees.  Filtering per
    -- tree would make `applyVerboseStepFilter` miss the boundaries and leave body
    -- tactics unfiltered.  Combining all trees first ensures boundaries and bodies
    -- are visible together before the step filter runs.
    let allRaw := resolvedTrees.foldl (fun acc t =>
      acc ++ collectTacticInfos none t #[]) #[]
    let tacticInfos :=
      let filtered :=
        if filterVerboseSteps then applyVerboseStepFilter allRaw inputCtx.fileMap
        else allRaw
      skipLastPerDeclaration filtered inputCtx.fileMap
    -- Only probe Verbose Lean proofs; skip commands with no Verbose tactics.
    if resolvedTrees.any treeContainsVerbose then
      let mut commandProbeAttempts := 0
      let mut commandSuccesses := 0
      -- Track the current declaration group to compute proof-relative line numbers.
      -- `tacticInfos` is sorted by source position after the filter pipeline, so
      -- the first tactic seen for each group gives the proof start line.
      let mut currentDecl : Option Name := none
      let mut proofStartLine : Nat := 1
      let mut exerciseName : String := "example"
      let mut groupSeen : Bool := false
      for (ci, ti) in tacticInfos do
        let pos := ci.fileMap.toPosition (ti.stx.getPos?.getD 0)
        let decl := ci.parentDecl?
        if !groupSeen || decl != currentDecl then
          currentDecl := decl
          proofStartLine := pos.line
          groupSeen := true
          exerciseName := match decl with
            | some name => name.toString
            | none      => findExerciseName sourceForNames pos.line
        let lineInProof := pos.line - proofStartLine + 1
        for goal in ti.goalsBefore do
          for tacticStr in probeTactics do
            commandProbeAttempts := commandProbeAttempts + 1
            let succeeded ← tryTacticAt ci ti.mctxBefore goal tacticStr
            if let some cb := onProbe then
              cb pos.line pos.column tacticStr succeeded
            if succeeded then
              commandSuccesses := commandSuccesses + 1
              results := results.push {
                file        := displayPath.toString
                line        := pos.line
                column      := pos.column
                exercise    := exerciseName
                lineInProof := lineInProof
                tactic      := tacticStr
              }
    state := newState
    done := isDone
    cmdIdx := cmdIdx + 1
  return results.foldl (fun acc r => if acc.contains r then acc else acc.push r) #[]

/-- A cache mapping import-header text to compiled environments.

    Reusing environments across files with the same imports avoids redundant
    `.olean` loading, which is the dominant cost when processing files that
    transitively import Mathlib (e.g. via `Verbose.English.All`).  The cache
    key is the raw import-header text, so files with identical imports share
    one compiled `Environment` instead of each paying the full loading cost. -/
abbrev EnvCache := IO.Ref (Array (String × Environment))

/-- Create a fresh empty environment cache. -/
def mkEnvCache : IO EnvCache := IO.mkRef #[]

/-- Look up or build the environment for a set of imports.
    `key` uniquely identifies the import set (e.g. the raw header text).
    `build` is called only on a cache miss to produce the `Environment`. -/
def getOrBuildEnv
    (cache : EnvCache) (key : String) (build : IO Environment) : IO Environment := do
  let cached ← cache.get
  match cached.find? (fun (k, _) => k == key) with
  | some (_, env) => return env
  | none =>
    let env ← build
    cache.modify (fun arr => arr.push (key, env))
    return env

/-- Analyse a single Lean source file, returning every (position, tactic) pair
    where a probe tactic succeeds.

    Uses `Frontend.FrontendM` with `snap? := none` and `Elab.async = false`
    so theorem bodies are elaborated synchronously and `TacticInfo` nodes are
  accumulated directly in `commandState.infoState.trees`. -/
def analyzeFile
    (filePath : System.FilePath) (probeTactics : Array String)
    (filterVerboseSteps : Bool := false)
  (onProbe : Option (Nat → Nat → String → Bool → IO Unit) := none) :
    IO (Array ProbeResult) := do
  -- Ensure the Lean stdlib .olean files are findable at runtime.
  -- `initSearchPath` also calls `addSearchPathFromEnv` which picks up the
  -- `LEAN_PATH` that Lake sets before running the binary, making imports from
  -- project dependencies (e.g. WaterproofGenre, Verbose) available.
  Lean.initSearchPath (← Lean.findSysroot)
  -- Allow [init] declarations to be executed when importing modules
  unsafe Lean.enableInitializersExecution
  let input ← IO.FS.readFile filePath
  let directResults ← analyzeInput filePath input probeTactics filterVerboseSteps (onProbe := onProbe)
  let merged ← match extractLeanFenceOverlay? input with
    | some overlay =>
      let overlayResults ← analyzeInput filePath overlay probeTactics filterVerboseSteps
        (onProbe := onProbe) (originalSource := input)
      pure (directResults ++ overlayResults)
    | none =>
      pure directResults
  return merged.foldl (fun acc r => if acc.contains r then acc else acc.push r) #[]

/-- Debug utility: run the filter pipeline on `filePath` and return a human-readable
    log showing, for each command, the raw tactic positions, positions after
    `applyVerboseStepFilter`, and positions after `skipLastPerDeclaration`.
    Operates on the fence-overlay (same path as `analyzeFile`). -/
def dumpFilterStages (filePath : System.FilePath) : IO String := do
  Lean.initSearchPath (← Lean.findSysroot)
  unsafe Lean.enableInitializersExecution
  let input ← IO.FS.readFile filePath
  let src := (extractLeanFenceOverlay? input).getD input
  let opts := Elab.async.set Options.empty false
  let inputCtx := Parser.mkInputContext src filePath.toString
  let (header, parserState, _) ← Parser.parseHeader inputCtx
  let (env, _) ← processHeader header opts {} inputCtx
  let initCmdState := Command.mkState env {} opts
  let ctx : Frontend.Context := { inputCtx }
  let initState : Frontend.State := { commandState := initCmdState, parserState, cmdPos := 0 }
  let fmtRow (ci : ContextInfo) (ti : TacticInfo) :=
    let pos := ci.fileMap.toPosition (ti.stx.getPos?.getD 0)
    s!"\n      {pos.line}:{pos.column} {ti.stx.getKind}"
  let mut log := ""
  let mut state := initState
  let mut cmdIdx := 0
  let mut done := false
  while !done do
    let (isDone, newState) ← (Frontend.processCommand.run ctx).run state
    let assignment := newState.commandState.infoState.assignment
    let resolvedTrees := newState.commandState.infoState.trees.toArray.map fun t =>
      t.substitute assignment
    let raw := resolvedTrees.foldl (fun acc t => acc ++ collectTacticInfos none t #[]) #[]
    if !raw.isEmpty then
      let filtered  := applyVerboseStepFilter raw inputCtx.fileMap
      let skipped   := skipLastPerDeclaration filtered inputCtx.fileMap
      let rawLog    := raw.foldl      (fun s (ci, ti) => s ++ fmtRow ci ti) ""
      let filtLog   := filtered.foldl (fun s (ci, ti) => s ++ fmtRow ci ti) ""
      let skipLog   := skipped.foldl  (fun s (ci, ti) => s ++ fmtRow ci ti) ""
      log := log ++ s!"\n  cmd {cmdIdx}:\n    [raw]{rawLog}\n    [filtered]{filtLog}\n    [skipped]{skipLog}"
    state := newState
    done := isDone
    cmdIdx := cmdIdx + 1
  return log

end Goudlokje
