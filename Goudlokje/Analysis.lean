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
  file   : String
  line   : Nat
  column : Nat
  tactic : String
  deriving Repr, BEq, Inhabited, ToJson, FromJson

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

    Kind names discovered empirically:
    - `Lean.Parser.Term.byTactic` — Lean core `by` block (as a term)
    - `by`                         — `by` as a tactic-level syntax node
    - `Lean.Parser.Tactic.tacticSeq` / `tacticSeq1Indented` — sequence containers
    - `Verbose.English.withSuggestions` — Verbose/English/Widget.lean
    - `Verbose.French.withSuggestions`  — Verbose/French/Widget.lean
    - `withoutSuggestions`              — Verbose/Tactics/Statements.lean -/
private def isSyntheticTacticContainer (ti : TacticInfo) : Bool :=
  let k := ti.stx.getKind.toString
  k == "Lean.Parser.Term.byTactic"                ||
  k == "by"                                       ||
  k == "Lean.Parser.Tactic.tacticSeq"             ||
  k == "Lean.Parser.Tactic.tacticSeq1Indented"    ||
  k == "Verbose.English.withSuggestions"           ||
  k == "Verbose.French.withSuggestions"            ||
  k == "withoutSuggestions"

/-- Collect (ContextInfo, TacticInfo) pairs from an InfoTree.
    We use `PartialContextInfo.mergeIntoOuter?` to resolve the full `ContextInfo`.
    Synthetic container nodes (`by` blocks, tactic sequences, Verbose proof wrappers)
    are excluded via `isSyntheticTacticContainer`. -/
private partial def collectTacticInfos
    (ci? : Option ContextInfo) (tree : InfoTree)
    (acc : Array (ContextInfo × TacticInfo)) : Array (ContextInfo × TacticInfo) :=
  match tree with
  | .context pci child =>
    let newCi? := pci.mergeIntoOuter? ci?
    collectTacticInfos newCi? child acc
  | .node info children =>
    let acc' := match ci?, info with
      | some ci, .ofTacticInfo ti =>
        if !ti.goalsBefore.isEmpty && !isSyntheticTacticContainer ti then acc.push (ci, ti) else acc
      | _, _ => acc
    children.foldl (fun a c => collectTacticInfos ci? c a) acc'
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
private partial def processCommandsCollectTrees
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

/-- Return true if the tactic is a Lean Verbose step-boundary tactic.
    These tactics introduce a new sub-goal (the "step goal") in a Verbose proof.
    Kind names discovered empirically by inspecting the Verbose English library. -/
private def isVerboseStepBoundary (ti : TacticInfo) : Bool :=
  let k := ti.stx.getKind.toString
  k == "tacticLet'sFirstProveThat_" ||
  k == "tacticLet'sNowProveThat_"   ||
  k == "tacticLet'sProveThat_Works_"

/-- When `filterVerboseSteps` is true, keep only the first non-boundary tactic per
    Verbose step, within each declaration.  Declarations without any step boundary
    keep ALL their tactics (they are not Verbose-style and must not be suppressed).

    Filtering is applied per-declaration (grouped by `parentDecl?`) so that filter
    state does not leak across independent theorems and exercises.  Without this
    isolation, a Verbose-style example earlier in the file would cause the filter to
    suppress all tactics in a later exercise that has no step boundaries of its own. -/
private def applyVerboseStepFilter
    (infos : Array (ContextInfo × TacticInfo)) (fileMap : FileMap) :
    Array (ContextInfo × TacticInfo) :=
  -- Early exit: no step boundaries present → no filtering needed
  if !infos.any (fun (_, ti) => isVerboseStepBoundary ti) then infos
  else
    -- Sort by source position
    let withPos := infos.map fun (ci, ti) =>
      (fileMap.toPosition (ti.stx.getPos?.getD 0), ci, ti)
    let sorted := withPos.toList.mergeSort (fun (p1, _, _) (p2, _, _) =>
      p1.line < p2.line || (p1.line == p2.line && p1.column < p2.column))
    -- Group consecutive tactics by enclosing declaration (parentDecl?).
    -- foldl over the sorted list accumulates groups in reverse with items within
    -- each group also reversed; we reverse both at the end to restore source order.
    let groups : List (Option Name × List (ContextInfo × TacticInfo)) :=
      sorted.foldl (fun acc (_, ci, ti) =>
        let decl := ci.parentDecl?
        match acc with
        | [] => [(decl, [(ci, ti)])]
        | (d, items) :: rest =>
          if d == decl then (d, (ci, ti) :: items) :: rest
          else (decl, [(ci, ti)]) :: acc)
        []
    -- For each group: if the group has step boundaries, apply the step filter
    -- (keep only the first non-boundary tactic per step).  Otherwise keep all
    -- (the declaration is not a Verbose-style proof).
    let filterGroup (items : List (ContextInfo × TacticInfo)) :
        List (ContextInfo × TacticInfo) :=
      if !items.any (fun (_, ti) => isVerboseStepBoundary ti) then
        items  -- No step boundaries in this declaration → keep all
      else
        let (result, _, _) := items.foldl
          (fun (acc : Array (ContextInfo × TacticInfo) × Bool × Bool) (ci, ti) =>
            let (result, inStep, stepGotFirst) := acc
            if isVerboseStepBoundary ti then
              (result, true, false)
            else if inStep && !stepGotFirst then
              (result.push (ci, ti), true, true)
            else
              (result, inStep, stepGotFirst))
          (#[], false, false)
        result.toList
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
    where a probe tactic succeeds. -/
private def analyzeInput
    (displayPath : System.FilePath) (input : String) (probeTactics : Array String)
    (filterVerboseSteps : Bool := false)
    (onProbe : Option (Nat → Nat → String → Bool → IO Unit) := none) :
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
    let tacticInfos :=
      resolvedTrees.foldl (fun acc t =>
        let raw := collectTacticInfos none t #[]
        let filtered :=
          if filterVerboseSteps then applyVerboseStepFilter raw inputCtx.fileMap else raw
        acc ++ skipLastPerDeclaration filtered inputCtx.fileMap) #[]
    let mut commandProbeAttempts := 0
    let mut commandSuccesses := 0
    for (ci, ti) in tacticInfos do
      let pos := ci.fileMap.toPosition (ti.stx.getPos?.getD 0)
      for goal in ti.goalsBefore do
        for tacticStr in probeTactics do
          commandProbeAttempts := commandProbeAttempts + 1
          let succeeded ← tryTacticAt ci ti.mctxBefore goal tacticStr
          if let some cb := onProbe then
            cb pos.line pos.column tacticStr succeeded
          if succeeded then
            commandSuccesses := commandSuccesses + 1
            results := results.push {
              file   := displayPath.toString
              line   := pos.line
              column := pos.column
              tactic := tacticStr
            }
    state := newState
    done := isDone
    cmdIdx := cmdIdx + 1
  return results.foldl (fun acc r => if acc.contains r then acc else acc.push r) #[]

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
      let overlayResults ← analyzeInput filePath overlay probeTactics filterVerboseSteps (onProbe := onProbe)
      pure (directResults ++ overlayResults)
    | none =>
      pure directResults
  return merged.foldl (fun acc r => if acc.contains r then acc else acc.push r) #[]

end Goudlokje
