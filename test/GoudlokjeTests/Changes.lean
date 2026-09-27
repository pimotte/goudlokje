import Goudlokje.Cli.Changes

/-! Tests for the changes `goudlokje update` proposes. -/

open Goudlokje Goudlokje.Cli

private def expectations (entries : List (String × ExerciseExpectations)) : Expectations :=
  { exercises := entries.foldl (fun m (k, v) => m.insert k v) {} }

private def finding (exercise : String) (check : Check) (step : Nat)
    (tactic? : Option String := none) : Finding :=
  { check, exercise, step, line := 0, column := 0, tactic?, message := "" }

private def allChecks : Array String := #["shortcut", "rawTactic", "typeAscription", "sorry"]

-- Unexpected findings are recorded, except raw tactics; expected findings are left alone.
#guard proposeChanges (expectations [("a", { shortcuts := #[{ step := 1, tactic := "simp" }] })]) {
    exercises := ({} : Std.HashMap _ _).insert "a" allChecks
    findings := #[finding "a" .shortcut 2 "decide", finding "a" .shortcut 1 "simp",
      finding "a" .typeAscription 3, finding "a" .rawTactic 4, finding "a" .sorry 5,
      finding "a" .sorry 6] } ==
  #[.recordShortcut "a" { step := 2, tactic := "decide" },
    .recordLint "a" { check := "typeAscription", step := 3 }, .allowSorry "a"]

-- Stale expectations are removed only for checks that ran.
private def old := expectations [("a", {
  shortcuts := #[{ step := 1, tactic := "decide" }]
  lint := #[{ check := "typeAscription", step := 2 }], allowSorry := true })]

#guard proposeChanges old { exercises := ({} : Std.HashMap _ _).insert "a" allChecks } ==
  #[.removeShortcut "a" { step := 1, tactic := "decide" },
    .removeLint "a" { check := "typeAscription", step := 2 }, .disallowSorry "a"]

#guard proposeChanges old { exercises := ({} : Std.HashMap _ _).insert "a" #["rawTactic"] } == #[]

-- `rawTactic` and unknown lint entries are invalid and removed automatically.
#guard
  let changes := proposeChanges
    (expectations [("a", { lint := #[{ check := "rawTactic", step := 1 }, { check := "x", step := 2 }] })])
    { exercises := ({} : Std.HashMap _ _).insert "a" #[] }
  changes.size == 2 && changes.all (·.automatic)

-- Exercises that no longer exist are removed; skipped exercises (with errors) are kept.
#guard proposeChanges (expectations [("gone", { allowSorry := true }), ("broken", { allowSorry := true })])
    { skipped := ({} : Std.HashSet _).insert "broken" } ==
  #[.removeExercise "gone"]

-- Applying changes; exercises without expectations are dropped.
#guard ((Change.recordShortcut "a" { step := 1, tactic := "decide" }).apply {}).get "a" ==
  { shortcuts := #[{ step := 1, tactic := "decide" }] }
#guard ((Change.disallowSorry "a").apply (expectations [("a", { allowSorry := true })])).exercises.isEmpty
