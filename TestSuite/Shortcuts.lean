import Goudlokje.Shortcuts

namespace TestSuite.Shortcuts

open Goudlokje

private def mkProbe (exercise : String) (stepNumber : Nat) (tacticIndexInStep : Nat) (tactic : String) : ProbeResult :=
  { file := "test.lean", line := 0, column := 0, exercise,
    id := { exercise, stepNumber, tacticIndexInStep }, tactic }

private def mkExpected (exercise : String) (stepNumber : Nat) (tacticIndexInStep : Nat) (tactic : String) : ExpectedShortcut :=
  { exercise, stepNumber, tacticIndexInStep, tactic }

private def assertEq [BEq α] [Repr α] (expected actual : α) (msg : String) : IO Unit :=
  unless expected == actual do
    throw (IO.userError s!"{msg}: expected {repr expected}, got {repr actual}")

def testEmptyFoundEmptyExpected : IO Unit := do
  let result := classify #[] { expected := #[] }
  assertEq 0 result.shortcuts.size "testEmpty: shortcuts"
  assertEq 0 result.stale.size     "testEmpty: stale"

def testUnexpectedShortcut : IO Unit := do
  let found := #[mkProbe "foo" 1 1 "ring"]
  let result := classify found { expected := #[] }
  assertEq 1 result.shortcuts.size "testUnexpected: size"
  assertEq 0 result.stale.size     "testUnexpected: stale"
  match result.shortcuts[0]! with
  | .unexpected _ => pure ()
  | .expected _   => throw (IO.userError "testUnexpected: got .expected, want .unexpected")

def testExpectedShortcut : IO Unit := do
  let found := #[mkProbe "foo" 1 1 "ring"]
  let tf : TestFile := { expected := #[mkExpected "foo" 1 1 "ring"] }
  let result := classify found tf
  assertEq 1 result.shortcuts.size "testExpected: size"
  assertEq 0 result.stale.size     "testExpected: stale"
  match result.shortcuts[0]! with
  | .expected _   => pure ()
  | .unexpected _ => throw (IO.userError "testExpected: got .unexpected, want .expected")

def testStaleEntry : IO Unit := do
  let tf : TestFile := { expected := #[mkExpected "foo" 1 1 "ring"] }
  let result := classify #[] tf
  assertEq 0 result.shortcuts.size "testStale: shortcuts"
  assertEq 1 result.stale.size     "testStale: stale"

def testMixedResults : IO Unit := do
  let found := #[
    mkProbe "foo" 1 1 "ring",   -- unexpected
    mkProbe "foo" 2 1 "omega"   -- expected
  ]
  let tf : TestFile := { expected := #[mkExpected "foo" 2 1 "omega"] }
  let result := classify found tf
  assertEq 2 result.shortcuts.size "testMixed: size"
  assertEq 0 result.stale.size     "testMixed: stale"
  let unexpectedCount := result.shortcuts.filter
    (fun s => match s with | .unexpected _ => true | _ => false) |>.size
  let expectedCount := result.shortcuts.filter
    (fun s => match s with | .expected _ => true | _ => false) |>.size
  assertEq 1 unexpectedCount "testMixed: unexpectedCount"
  assertEq 1 expectedCount   "testMixed: expectedCount"

def testMatchRequiresAllFields : IO Unit := do
  -- Same position but different tactic → should be unexpected
  let found := #[mkProbe "foo" 1 1 "ring"]
  let tf : TestFile := { expected := #[mkExpected "foo" 1 1 "omega"] }
  let result := classify found tf
  assertEq 1 result.stale.size "testMatchFields: stale"
  match result.shortcuts[0]! with
  | .unexpected _ => pure ()
  | .expected _   => throw (IO.userError "testMatchFields: should not match on tactic mismatch")

def testMatchRequiresSameExercise : IO Unit := do
  -- Same stepNumber and tactic but different exercise → should be unexpected
  let found := #[mkProbe "bar" 1 1 "ring"]
  let tf : TestFile := { expected := #[mkExpected "foo" 1 1 "ring"] }
  let result := classify found tf
  assertEq 1 result.stale.size "testMatchExercise: stale"
  match result.shortcuts[0]! with
  | .unexpected _ => pure ()
  | .expected _   => throw (IO.userError "testMatchExercise: should not match on exercise mismatch")

def testMatchRequiresSameStep : IO Unit := do
  -- Same exercise and tactic but different stepNumber → should be unexpected
  let found := #[mkProbe "foo" 2 1 "ring"]
  let tf : TestFile := { expected := #[mkExpected "foo" 1 1 "ring"] }
  let result := classify found tf
  assertEq 1 result.stale.size "testMatchStep: stale"
  match result.shortcuts[0]! with
  | .unexpected _ => pure ()
  | .expected _   => throw (IO.userError "testMatchStep: should not match on stepNumber mismatch")

def testTacticIndexNotUsedForMatching : IO Unit := do
  -- Same exercise, step, and tactic but different tacticIndexInStep → should match
  -- This tests that tacticIndexInStep is stored but not used for matching
  let found := #[mkProbe "foo" 1 2 "ring"]
  let tf : TestFile := { expected := #[mkExpected "foo" 1 1 "ring"] }
  let result := classify found tf
  assertEq 1 result.shortcuts.size "testIndexNotUsed: size"
  assertEq 0 result.stale.size     "testIndexNotUsed: stale"
  match result.shortcuts[0]! with
  | .expected _   => pure ()
  | .unexpected _ => throw (IO.userError "testIndexNotUsed: should match ignoring tacticIndexInStep")

def testMultipleStale : IO Unit := do
  let tf : TestFile := {
    expected := #[
      mkExpected "ex1" 1 1 "ring",
      mkExpected "ex2" 2 1 "omega"
    ]
  }
  let result := classify #[] tf
  assertEq 2 result.stale.size "testMultipleStale"

def testWithinStepEditDoesNotBreakMatching : IO Unit := do
  -- Simulates: a new tactic was added before this one, shifting tacticIndexInStep.
  -- The old entry has tacticIndexInStep=1, the probe now finds it at tacticIndexInStep=2.
  -- Since matching ignores tacticIndexInStep, this should still match.
  let found := #[mkProbe "exercise1" 1 2 "exact rfl"]
  let tf : TestFile := { expected := #[mkExpected "exercise1" 1 1 "exact rfl"] }
  let result := classify found tf
  assertEq 1 result.shortcuts.size "testWithinStepEdit: size"
  assertEq 0 result.stale.size     "testWithinStepEdit: stale"
  match result.shortcuts[0]! with
  | .expected _   => pure ()
  | .unexpected _ => throw (IO.userError "testWithinStepEdit: should match ignoring tacticIndexInStep")

def runAll : IO Unit := do
  testEmptyFoundEmptyExpected;       IO.println "  ✓ testEmptyFoundEmptyExpected"
  testUnexpectedShortcut;            IO.println "  ✓ testUnexpectedShortcut"
  testExpectedShortcut;              IO.println "  ✓ testExpectedShortcut"
  testStaleEntry;                    IO.println "  ✓ testStaleEntry"
  testMixedResults;                  IO.println "  ✓ testMixedResults"
  testMatchRequiresAllFields;        IO.println "  ✓ testMatchRequiresAllFields"
  testMatchRequiresSameExercise;     IO.println "  ✓ testMatchRequiresSameExercise"
  testMatchRequiresSameStep;         IO.println "  ✓ testMatchRequiresSameStep"
  testTacticIndexNotUsedForMatching; IO.println "  ✓ testTacticIndexNotUsedForMatching"
  testMultipleStale;                 IO.println "  ✓ testMultipleStale"
  testWithinStepEditDoesNotBreakMatching; IO.println "  ✓ testWithinStepEditDoesNotBreakMatching"

end TestSuite.Shortcuts
