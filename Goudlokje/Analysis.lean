import Lean
import Lean.Elab.Frontend
import Lean.Elab.Tactic
import Lean.Elab.Import
import Lean.Meta

/-! # Goudlokje.Analysis

Core file analysis engine for Goudlokje.

This module implements InfoTree traversal (`collectTacticInfos`) and goal-state
replay (`tryTacticAt`) from scratch rather than delegating to the
`Mathlib.Tactic.TacticAnalysis` framework.  The rationale — monad mismatch,
missing Verbose-wrapper filtering, and linter-only API — is documented in full
in the `analyzeFile` docstring below. -/

namespace Goudlokje

open Lean Elab Meta

/-- A position in a source file where a probe tactic succeeded. -/
structure ProbeResult where
  file   : String
  line   : Nat
  column : Nat
  tactic : String
  deriving Repr, BEq, Inhabited

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
    are excluded via `isSyntheticTacticContainer`.

    **Why not use `Mathlib.Tactic.TacticAnalysis.findTacticSeqs`?**
    This function is implemented from scratch rather than delegating to the Mathlib
    framework.  The full rationale is in the `analyzeFile` docstring; briefly:
    (1) `findTacticSeqs` lives in `CommandElabM`, which cannot be bridged to `IO`
        without complex glue code that is more fragile than this traversal;
    (2) it does not filter Verbose proof-wrapper nodes, so we need our own
        `isSyntheticTacticContainer` regardless; and
    (3) the high-level Mathlib API is a linter, not a batch-analysis primitive,
        so it cannot return results or signal failures for Goudlokje's CI use case.
    The custom traversal is therefore the simpler and more appropriate solution. -/
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
    Returns `true` if the tactic closes the first goal.

    **Why not use `Lean.Elab.ContextInfo.runTacticCode`?**
    The Mathlib counterpart lives in `CommandElabM`; see `collectTacticInfos` and
    the `analyzeFile` docstring for the full rationale. -/
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

/-- Group non-boundary tactics by Verbose step for a tree that contains step boundaries.

    `afterSkipLast` contains the tactics to group (step boundaries already removed,
    skip-last already applied).  `raw` contains all tactics from the tree including
    step boundaries, used solely to locate group boundaries.

    Returns an array of step groups; each inner array holds the tactics for one
    Verbose step in source order.  Tactics that appear before the first boundary
    (rare) form their own leading group.

    The caller probes each group in order and reports only the **first** successful
    probe per group, implementing "report first shortcut per step" semantics:
    - If the first tactic in a step is shortcuttable it is reported and the rest of
      the step is skipped.
    - If the first tactic is *not* shortcuttable, the remaining tactics in the step
      are probed in order until a shortcut is found (or the step is exhausted). -/
private def groupByVerboseStep
    (afterSkipLast : Array (ContextInfo × TacticInfo))
    (raw : Array (ContextInfo × TacticInfo))
    (fileMap : FileMap) :
    Array (Array (ContextInfo × TacticInfo)) :=
  -- Set of source positions that survived skip-last (used to skip dropped tactics)
  let survivorPos := afterSkipLast.map (fun (_, ti) => ti.stx.getPos?.getD 0)
  let lt (a b : ContextInfo × TacticInfo) : Bool :=
    let p1 := fileMap.toPosition (a.2.stx.getPos?.getD 0)
    let p2 := fileMap.toPosition (b.2.stx.getPos?.getD 0)
    p1.line < p2.line || (p1.line == p2.line && p1.column < p2.column)
  let sortedRaw := raw.toList.mergeSort lt
  let (groups, currentGroup) := sortedRaw.foldl
    (fun (acc : Array (Array (ContextInfo × TacticInfo)) × Array (ContextInfo × TacticInfo))
         (ci, ti) =>
      let (gs, cur) := acc
      if isVerboseStepBoundary ti then
        -- Start a new step group; push current group if non-empty
        (if cur.isEmpty then gs else gs.push cur, #[])
      else if survivorPos.contains (ti.stx.getPos?.getD 0) then
        -- Eligible tactic: append to current group
        (gs, cur.push (ci, ti))
      else
        -- Dropped by skip-last: skip
        (gs, cur))
    (#[], #[])
  if currentGroup.isEmpty then groups else groups.push currentGroup

/-- For each declaration in `infos`, drop **all** tactic nodes at the last source
    position (by source order).
    A shortcut at the final step of a proof never saves proof lines — the student
    must still write that step (or an equivalent).  Skipping it avoids false positives
    where a probe tactic can close the goal at the last line of an exercise.

    We drop ALL nodes at the last position, not just one.  Lean Verbose phrases such
    as `We compute` expand via macros and can produce multiple `TacticInfo` nodes
    at the same source position (the phrase itself and its inner tactic).  Using a
    simple `dropLast` would leave one of those nodes behind, causing a false positive.

    Grouping follows the same consecutive-`parentDecl?` logic as the step filter:
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
  -- Restore source order and drop ALL tactics at the last source position of each group.
  let dropLastPos (items : List (ContextInfo × TacticInfo)) (fileMap : FileMap) :
      List (ContextInfo × TacticInfo) :=
    match items.getLast? with
    | none => []
    | some (_, lastTi) =>
      let lastPos := fileMap.toPosition (lastTi.stx.getPos?.getD 0)
      items.filter fun (_, ti) =>
        fileMap.toPosition (ti.stx.getPos?.getD 0) != lastPos
  let allResults :=
    groups.reverse.foldl (fun acc (_, items) =>
      acc ++ dropLastPos items.reverse fileMap)
      []
  allResults.toArray

/-- A cache mapping import-header text to compiled environments.
    Reusing environments across files with the same imports avoids redundant
    `.olean` loading (the dominant cost for files that import Mathlib). -/
abbrev EnvCache := IO.Ref (Array (String × Environment))

/-- Create a fresh empty environment cache. -/
def mkEnvCache : IO EnvCache := IO.mkRef #[]

/-- Look up or build the environment for a set of imports.
    `key` uniquely identifies the import set (e.g. the raw header text).
    `build` is called only on a cache miss to produce the `Environment`. -/
private def getOrBuildEnv
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
    accumulated directly in `commandState.infoState.trees`.

    If `envCache` is provided, the compiled environment for the file's imports
    is reused across files with identical import lists, avoiding redundant
    `.olean` loading.

    **Attempted refactoring to use `Mathlib.TacticAnalysis` (and why it was abandoned)**

    We attempted to replace the custom InfoTree traversal and tactic-replay
    logic with Mathlib's `Mathlib.Tactic.TacticAnalysis` framework.  The
    attempt revealed three independent reasons the framework cannot be used
    here, even if this tool is run through `lake build`.

    *1. Monad mismatch: `CommandElabM` vs `IO`.*
    `Mathlib.TacticAnalysis.findTacticSeqs` and
    `Lean.Elab.ContextInfo.runTacticCode` (the two primitives that would
    replace `collectTacticInfos` and `tryTacticAt`) both live in
    `CommandElabM = ReaderT Context $ StateRefT State $ EIO Exception`.
    Goudlokje elaborates files from plain `IO` via `Frontend.FrontendM`.
    Bridging the two requires (a) constructing a `Command.Context` with all
    required fields (`snap?`, `cancelTk?`, …), (b) allocating an `IO.Ref`
    for the command state, and (c) converting `EIO Lean.Exception` errors
    back to `IO.Error`.  The resulting glue code is more complex than the
    `MetaM`-level helpers it replaces, and it is fragile with respect to
    future changes to `Command.Context`.

    *2. Missing Verbose-wrapper filter.*
    `findTacticSeqs` filters `tacticSeq`, `tacticSeq1Indented`, and
    `byTactic` nodes, but it does **not** filter the Verbose proof-wrapper
    tactics (`withoutSuggestions`, `Verbose.English.withSuggestions`,
    `Verbose.French.withSuggestions`).  Without filtering these, a spurious
    tactic node at the `Proof:` position (with a non-empty `goalsBefore`)
    is included, causing false-positive shortcut reports.  We would have to
    re-add `isSyntheticTacticContainer`-style filtering on top of the
    Mathlib traversal, so the custom code would not be eliminated.

    *3. Architectural incompatibility with the linter-based API.*
    The high-level API (`tryAtEachStepFromStrings`, `@[tacticAnalysis]`,
    `runPasses`) is a *linter* that fires on the file currently being
    compiled by `lake build`.  Goudlokje analyses **external** worksheet
    files that are not part of the Goudlokje project, so there is no
    compilation unit in which to register the linter.  Furthermore, the
    linter only emits messages; it cannot compare results against a
    `.test.json` expected-shortcuts file or return a non-zero exit code
    for CI, both of which are core requirements of Goudlokje's check mode.

    **Conclusion**: The `MetaM`-level helpers `collectTacticInfos` and
    `tryTacticAt` below implement the same ideas (InfoTree traversal with
    context threading, goal-state replay) at the correct abstraction layer
    for a standalone batch tool.  They are not reinventing the wheel so
    much as operating one layer below the linter framework, which is the
    only layer accessible from `IO`. -/
def analyzeFile
    (filePath : System.FilePath) (probeTactics : Array String)
    -- filterVerboseSteps: controls per-step shortcut deduplication for Lean Verbose files.
    --
    --   Step-boundary tactics (`Let's first prove that …`, `Let's now prove that …`) are
    --   **always** excluded from probing regardless of this flag — they are structural
    --   markers, not user proof steps.  This flag only affects how the remaining tactics
    --   inside each step body are reported.
    --
    --   *Enable* (`true`) when analysing Lean Verbose worksheet files whose proofs use
    --   step-boundary tactics.  With this flag, Goudlokje groups tactics by Verbose step
    --   and reports at most one shortcut per step — specifically the *first* tactic in
    --   the step that the probe can close.  If the first tactic in a step is not
    --   shortcuttable, subsequent tactics in the same step are probed in source order
    --   until a shortcut is found.  Without this flag, every tactic in every step body
    --   is reported separately, flooding the output with duplicate reports for the same
    --   exercise step.
    --
    --   *Disable* (`false`, the default) for plain Lean or Mathlib files that do not
    --   use Verbose step boundaries.  Enabling step grouping on such files would cause
    --   Goudlokje to report at most one shortcut per proof, missing later shortcuts.
    (filterVerboseSteps : Bool := false)
    (envCache : Option EnvCache := none)
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
  let opts  := Elab.async.set Options.empty false
  let inputCtx := Parser.mkInputContext input filePath.toString
  let (header, parserState, _messages) ← Parser.parseHeader inputCtx
  -- Cache key: all `import` lines at the top of the file (whitespace-terminated).
  -- Files sharing the same import set produce the same key and reuse the same env.
  let headerKey := "\n".intercalate
    (input.splitOn "\n" |>.takeWhile fun l =>
      l.startsWith "import " || l.startsWith "--" || l.isEmpty)
  let env ← match envCache with
    | some cache =>
      getOrBuildEnv cache headerKey do
        let (env, _) ← processHeader header opts {} inputCtx; pure env
    | none => do let (env, _) ← processHeader header opts {} inputCtx; pure env
  let initCmdState : Command.State := Command.mkState env {} opts
  let initState : Frontend.State := {
    commandState := initCmdState
    parserState  := parserState
    cmdPos       := 0
  }
  let ctx : Frontend.Context := { inputCtx }
  -- Collect trees from each command (each command's trees are reset before the next)
  let (allTrees, finalState) ← processCommandsCollectTrees ctx initState #[]
  -- Resolve any pending lazy assignments
  let assignment := finalState.commandState.infoState.assignment
  let resolvedTrees := allTrees.map fun t => t.substitute assignment
  -- Build step groups per tree.
  -- Each tree corresponds to one top-level command; step-boundary state and
  -- skip-last logic are applied independently per tree so they do not leak
  -- across commands.
  --
  -- When `filterVerboseSteps` is true and the tree contains Verbose step
  -- boundaries, tactics are grouped by step via `groupByVerboseStep`.  The
  -- probing loop below then reports at most one shortcut per group (the first
  -- tactic in the step that the probe can close).
  --
  -- When `filterVerboseSteps` is false, or when the tree has no step boundaries,
  -- each tactic becomes a singleton group so all shortcuts are reported.
  --
  -- `skipLastPerDeclaration` is applied before grouping: a shortcut at the final
  -- tactic of a proof never saves proof lines and must not be reported.
  let allGroups : Array (Array (ContextInfo × TacticInfo)) :=
    resolvedTrees.foldl (fun acc t =>
      let raw := collectTacticInfos none t #[]
      -- Always exclude step boundaries from probing: they are structural markers
      -- (e.g. `Let's first prove that …`), not user proof tactics.  They do appear
      -- in `raw` so that `groupByVerboseStep` can use them as group delimiters.
      let nonBoundary := raw.filter (fun (_, ti) => !isVerboseStepBoundary ti)
      let afterSkipLast := skipLastPerDeclaration nonBoundary inputCtx.fileMap
      let groups :=
        if filterVerboseSteps && raw.any (fun (_, ti) => isVerboseStepBoundary ti)
        then groupByVerboseStep afterSkipLast raw inputCtx.fileMap
        else afterSkipLast.map (fun pair => #[pair])
      acc ++ groups) #[]
  -- Probe each step group.
  -- Tactics in each group are probed in source order until the first shortcut is found:
  -- - If the first tactic in a group is shortcuttable, it is reported and the rest skipped.
  -- - If the first tactic is NOT shortcuttable, probing continues through the remaining
  --   tactics in the group until a shortcut is found (or the group is exhausted).
  -- For singleton groups (non-Verbose or no step boundaries), this reduces to reporting
  -- the shortcut if any; for multi-tactic Verbose step groups, at most one shortcut per
  -- step is reported (the first one found).
  let mut results : Array ProbeResult := #[]
  for group in allGroups do
    let mut groupDone := false
    for (ci, ti) in group do
      if !groupDone then
        let pos := ci.fileMap.toPosition (ti.stx.getPos?.getD 0)
        for goal in ti.goalsBefore do
          if !groupDone then
            for tacticStr in probeTactics do
              if !groupDone then
                let succeeded ← tryTacticAt ci ti.mctxBefore goal tacticStr
                if let some cb := onProbe then
                  cb pos.line pos.column tacticStr succeeded
                if succeeded then
                  results := results.push {
                    file   := filePath.toString
                    line   := pos.line
                    column := pos.column
                    tactic := tacticStr
                  }
                  groupDone := true
  -- Deduplicate: multiple InfoTree nodes can cover the same tactic step,
  -- and each goal in goalsBefore is probed independently, so the same
  -- (file, line, column, tactic) tuple can appear several times.
  return results.foldl (fun acc r => if acc.contains r then acc else acc.push r) #[]

end Goudlokje
