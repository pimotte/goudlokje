import Goudlokje.Cli.Results

/-!
# Changes to `.test.json`

Given a worksheet's current `.test.json` and the results of checking it (the records the linter
writes to the results file), `proposeChanges` computes the changes `goudlokje update` proposes:
record new findings as expected, and remove expectations that are stale.
-/

namespace Goudlokje.Cli

open Lean

/-- A change to a `.test.json` file. -/
inductive Change where
  | recordShortcut (exercise : String) (entry : ExpectedShortcut)
  | recordLint (exercise : String) (entry : ExpectedLint)
  | allowSorry (exercise : String)
  | removeShortcut (exercise : String) (entry : ExpectedShortcut)
  | removeLint (exercise : String) (entry : ExpectedLint)
  | disallowSorry (exercise : String)
  /-- Remove all expectations of an exercise that no longer exists. -/
  | removeExercise (exercise : String)
  deriving Repr, BEq

namespace Change

/-- The exercise the change is about. -/
def exercise : Change → String
  | recordShortcut e _ | recordLint e _ | allowSorry e | removeShortcut e _ | removeLint e _
  | disallowSorry e | removeExercise e => e

/-- A description of the change, as a question. -/
def describe : Change → String
  | recordShortcut e s => s!"Record shortcut `{s.tactic}` at step {s.step} of {e.quote} as expected"
  | recordLint e l => s!"Record `{l.check}` at step {l.step} of {e.quote} as expected"
  | allowSorry e => s!"Allow `sorry` in {e.quote}"
  | removeShortcut e s =>
    s!"Remove the stale expected shortcut `{s.tactic}` at step {s.step} of {e.quote}"
  | removeLint e l => s!"Remove the stale expected `{l.check}` at step {l.step} of {e.quote}"
  | disallowSorry e => s!"Remove the stale `sorry` allowance of {e.quote}"
  | removeExercise e => s!"Remove the expectations of {e.quote}, which no longer exists"

/-- Whether the change is made without asking: removing entries that are invalid anyway. -/
def automatic : Change → Bool
  | removeLint _ l => !((Check.ofName? l.check).any (·.suppressible))
  | _ => false

/-- Applies the change to `e`. -/
def apply (c : Change) (e : Expectations) : Expectations :=
  let modify (f : ExerciseExpectations → ExerciseExpectations) : Expectations :=
    let updated := f (e.get c.exercise)
    { exercises :=
        if updated == {} then e.exercises.erase c.exercise
        else e.exercises.insert c.exercise updated }
  match c with
  | recordShortcut _ s => modify fun x => { x with shortcuts := x.shortcuts.push s }
  | recordLint _ l => modify fun x => { x with lint := x.lint.push l }
  | allowSorry _ => modify ({ · with allowSorry := true })
  | removeShortcut _ s => modify fun x => { x with shortcuts := x.shortcuts.erase s }
  | removeLint _ l => modify fun x => { x with lint := x.lint.erase l }
  | disallowSorry _ => modify ({ · with allowSorry := false })
  | removeExercise name => { exercises := e.exercises.erase name }

end Change

/-- The changes to `old` that the results `r` call for:

* unexpected findings are recorded as expected, except raw tactics, which cannot be;
* stale expectations of checked exercises are removed (see `ExerciseExpectations.stale`);
* expectations of exercises that were neither checked nor skipped are removed. -/
def proposeChanges (old : Expectations) (r : ModuleResults) : Array Change := Id.run do
  let mut changes : Array Change := #[]
  for (name, checks) in r.exercises.toArray.qsort (·.1 < ·.1) do
    let expected := old.get name
    let findings := r.findings.filter (·.exercise == name)
    -- New findings.
    for f in findings do
      if expected.expects f.check f.step f.tactic? then continue
      let change? : Option Change := match f.check with
        | .shortcut => f.tactic?.map fun tactic => .recordShortcut name { step := f.step, tactic }
        | .typeAscription => some (.recordLint name { check := f.check.name, step := f.step })
        | .sorry => some (.allowSorry name)
        | .rawTactic => none
      if let some change := change? then
        unless changes.contains change do changes := changes.push change
    -- Stale expectations.
    let ran := checks.filterMap Check.ofName?
    for entry in expected.stale ran (findings.map fun f => (f.check, f.step, f.tactic?)) do
      changes := changes.push <| match entry with
        | .shortcut s => .removeShortcut name s
        | .lint l _ => .removeLint name l
        | .allowSorry => .disallowSorry name
  -- Exercises that no longer exist.
  for (name, _) in old.exercises do
    unless r.exercises.contains name || r.skipped.contains name do
      changes := changes.push (.removeExercise name)
  return changes

end Goudlokje.Cli
