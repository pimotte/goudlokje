import Lean.Server.InfoUtils
import Goudlokje.Origin

/-!
# Proof steps

Extracts the user-written tactic steps of a command from its syntax and info trees.

A *step* is an item of a tactic sequence as written in the source (`tac₁; tac₂` or one tactic per
line), paired with the outermost `TacticInfo` elaborating exactly that syntax. Steps are found
through the command syntax rather than through the info trees, so macro expansions (such as the
internals of Verbose tactics) and synthetic wrappers (`by`, sequence nodes, the Verbose `Exercise`
proof wrapper) never become steps.
-/

namespace Goudlokje

open Lean Elab

/-- A user-written tactic step together with the elaboration info for it. -/
structure Step where
  /-- The tactic syntax as it appears in the source. -/
  stx  : Syntax
  /-- The context the tactic was elaborated in. -/
  ctx  : ContextInfo
  /-- The elaboration info of the tactic. -/
  info : TacticInfo

namespace Step

/-- The goal this step works on. -/
def mainGoal? (s : Step) : Option MVarId :=
  s.info.goalsBefore.head?

/-- Whether this step closes its main goal: every goal left afterwards was already open before,
    apart from the main goal. A step that leaves a new goal behind (a changed goal, subgoals) does
    not close its main goal, so some later step has to. -/
def closesMainGoal (s : Step) : Bool :=
  s.info.goalsAfter.all s.info.goalsBefore.tail.contains

/-- The goal that replaces the main goal after this step, if there is exactly one: the main goal
    itself if the step left it open, or else the single goal the step introduced (e.g. the
    changed goal after `show`). -/
def successorGoal? (s : Step) : Option MVarId := do
  let goal ← s.mainGoal?
  if s.info.goalsAfter.contains goal then return goal
  match s.info.goalsAfter.filter (!s.info.goalsBefore.contains ·) with
  | [next] => return next
  | _ => none

/-- The source line of the step. -/
def line (fileMap : FileMap) (s : Step) : Nat :=
  (fileMap.toPosition (s.stx.getPos?.getD 0)).line

/-- Whether the step is written with a Lean Verbose tactic, given the Verbose `modules` (see
    `verboseModules`). -/
def isVerbose (env : Environment) (modules : Array Name) (s : Step) : Bool :=
  isVerboseKind env modules s.stx.getKind

/-- The source position of the step, which identifies it within a command. -/
def pos (s : Step) : Nat :=
  (s.stx.getPos?.getD 0).byteIdx

end Step

/-- The number of step `s` among `steps`, the steps of its exercise in source order, starting at 1.
    Step numbers identify steps in `.test.json` files, so they stay valid when lines are added or
    removed outside the exercise, and when blank lines or comments are added inside it. -/
def stepNumber (steps : Array Step) (s : Step) : Nat :=
  (steps.findIdx? (·.pos == s.pos)).getD steps.size + 1

/-- Groups the probe points among `steps` (those that do not close their main goal) into goal
    chains: a step continues the chain of an earlier step when it works on that step's successor
    goal. All steps in a chain work towards the same proof obligation, so only the first shortcut
    in a chain is worth reporting. `steps` must be in execution order. -/
def goalChains (steps : Array Step) : Array (Array Step) := Id.run do
  let mut chains : Array (Array Step) := #[]
  let mut chainOf : Std.HashMap MVarId Nat := {}
  for step in steps do
    let some goal := step.mainGoal? | continue
    if step.closesMainGoal then continue
    let idx ← match chainOf[goal]? with
      | some idx => pure idx
      | none => do chains := chains.push #[]; pure (chains.size - 1)
    chains := chains.modify idx (·.push step)
    if let some next := step.successorGoal? then
      chainOf := chainOf.insert next idx
  return chains

/-- Tactics that only focus on a goal and contain a nested tactic sequence. They are not steps
    themselves; the tactics inside them are. -/
private def focusingKinds : Array SyntaxNodeKind :=
  #[``Lean.cdot, ``Lean.Parser.Tactic.case, `Lean.Parser.Tactic.«tacticNext_=>_»]

/-- The items of all (nested) tactic sequences in `stx`, excluding focusing tactics. -/
partial def tacticSeqItems (stx : Syntax) : Array Syntax :=
  go stx #[]
where
  go (stx : Syntax) (acc : Array Syntax) : Array Syntax :=
    let acc :=
      if stx.isOfKind ``Parser.Tactic.tacticSeq1Indented then
        pushItems stx[0].getSepArgs acc
      else if stx.isOfKind ``Parser.Tactic.tacticSeqBracketed then
        pushItems stx[1].getSepArgs acc
      else acc
    stx.getArgs.foldl (fun acc child => go child acc) acc
  pushItems (items : Array Syntax) (acc : Array Syntax) : Array Syntax :=
    items.foldl (init := acc) fun acc item =>
      if focusingKinds.contains item.getKind then acc else acc.push item

/-- The source range and kind identifying a piece of original syntax. -/
private def syntaxKey? (stx : Syntax) : Option (Nat × Nat × SyntaxNodeKind) := do
  let pos ← stx.getPos? (canonicalOnly := true)
  let tail ← stx.getTailPos? (canonicalOnly := true)
  return (pos.byteIdx, tail.byteIdx, stx.getKind)

/-- The steps of the command `cmd`, in source order, given the info trees it produced.
    Items without a `TacticInfo` that has open goals (e.g. not elaborated because of an error)
    are skipped. -/
def collectSteps (cmd : Syntax) (trees : PersistentArray InfoTree) : Array Step := Id.run do
  let items := tacticSeqItems cmd
  if items.isEmpty then return #[]
  let wanted : Std.HashSet (Nat × Nat × SyntaxNodeKind) :=
    items.foldl (init := {}) fun s item => (syntaxKey? item).elim s s.insert
  -- The info trees are traversed in pre-order, so the first `TacticInfo` found for a piece of
  -- syntax is the outermost one; macro expansions of it come later.
  let mut infos : Std.HashMap (Nat × Nat × SyntaxNodeKind) (ContextInfo × TacticInfo) := {}
  for tree in trees do
    infos := tree.foldInfo (init := infos) fun ctx info infos =>
      match info with
      | .ofTacticInfo ti =>
        match syntaxKey? ti.stx with
        | some key =>
          if wanted.contains key && !infos.contains key then infos.insert key (ctx, ti) else infos
        | none => infos
      | _ => infos
  let steps := items.filterMap fun item => do
    let (ctx, info) ← infos.get? (← syntaxKey? item)
    guard !info.goalsBefore.isEmpty
    return { stx := item, ctx, info }
  return steps.qsort (·.pos < ·.pos)

/-- The name of the exercise declared by `cmd`: the title of a Verbose `Exercise`/`Example`, the
    name of a named declaration, or for an anonymous `example` its statement (e.g.
    `example : 1 + 1 = 2`), which tells apart the examples in a file. -/
def exerciseName (env : Environment) (modules : Array Name) (cmd : Syntax) : String :=
  if isVerboseKind env modules cmd.getKind then
    (cmd.getArgs.findSome? (·.isStrLit?)).getD "example"
  else if let some declId := cmd.find? (·.isOfKind ``Parser.Command.declId) then
    declId[0].getId.toString
  else if let some sig := cmd.find? (·.isOfKind ``Parser.Command.optDeclSig) then
    let statement := (sig.getSubstring? (withLeading := false) (withTrailing := false)).map
      fun s => " ".intercalate (s.toString.splitToList Char.isWhitespace |>.filter (!·.isEmpty))
    match statement with
    | some statement => s!"example {statement}"
    | none => "example"
  else "example"

end Goudlokje
