import Goudlokje.Shortcuts

namespace TestSuite.Shortcuts

open Goudlokje

private def mkProbe (file : String) (line col : Nat) (tactic : String) : ProbeResult :=
  { file, line, column := col, tactic }

private def mkExpected (file : String) (line col : Nat) (tactic : String) : ExpectedShortcut :=
  { file, line, column := col, tactic }

private def assertEq [BEq α] [Repr α] (expected actual : α) (msg : String) : IO Unit :=
  unless expected == actual do
    throw (IO.userError s!"{msg}: expected {repr expected}, got {repr actual}")

def testEmptyFoundEmptyExpected : IO Unit := do
  let result := classify #[] { expected := #[] }
  assertEq 0 result.shortcuts.size "testEmpty: shortcuts"
  assertEq 0 result.stale.size     "testEmpty: stale"

def testUnexpectedShortcut : IO Unit := do
  let found := #[mkProbe "foo.lean" 10 4 "ring"]
  let result := classify found { expected := #[] }
  assertEq 1 result.shortcuts.size "testUnexpected: size"
  assertEq 0 result.stale.size     "testUnexpected: stale"
  match result.shortcuts[0]! with
  | .unexpected _ => pure ()
  | .expected _   => throw (IO.userError "testUnexpected: got .expected, want .unexpected")

def testExpectedShortcut : IO Unit := do
  let found := #[mkProbe "foo.lean" 10 4 "ring"]
  let tf : TestFile := { expected := #[mkExpected "foo.lean" 10 4 "ring"] }
  let result := classify found tf
  assertEq 1 result.shortcuts.size "testExpected: size"
  assertEq 0 result.stale.size     "testExpected: stale"
  match result.shortcuts[0]! with
  | .expected _   => pure ()
  | .unexpected _ => throw (IO.userError "testExpected: got .unexpected, want .expected")

def testStaleEntry : IO Unit := do
  let tf : TestFile := { expected := #[mkExpected "foo.lean" 10 4 "ring"] }
  let result := classify #[] tf
  assertEq 0 result.shortcuts.size "testStale: shortcuts"
  assertEq 1 result.stale.size     "testStale: stale"

def testMixedResults : IO Unit := do
  let found := #[
    mkProbe "foo.lean" 10 4 "ring",   -- unexpected
    mkProbe "foo.lean" 20 8 "omega"   -- expected
  ]
  let tf : TestFile := { expected := #[mkExpected "foo.lean" 20 8 "omega"] }
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
  let found := #[mkProbe "foo.lean" 10 4 "ring"]
  let tf : TestFile := { expected := #[mkExpected "foo.lean" 10 4 "omega"] }
  let result := classify found tf
  assertEq 1 result.stale.size "testMatchFields: stale"
  match result.shortcuts[0]! with
  | .unexpected _ => pure ()
  | .expected _   => throw (IO.userError "testMatchFields: should not match on tactic mismatch")

def testMultipleStale : IO Unit := do
  let tf : TestFile := {
    expected := #[
      mkExpected "a.lean" 1 0 "ring",
      mkExpected "b.lean" 5 2 "omega"
    ]
  }
  let result := classify #[] tf
  assertEq 2 result.stale.size "testMultipleStale"

def runAll : IO Unit := do
  testEmptyFoundEmptyExpected;  IO.println "  ✓ testEmptyFoundEmptyExpected"
  testUnexpectedShortcut;       IO.println "  ✓ testUnexpectedShortcut"
  testExpectedShortcut;         IO.println "  ✓ testExpectedShortcut"
  testStaleEntry;               IO.println "  ✓ testStaleEntry"
  testMixedResults;             IO.println "  ✓ testMixedResults"
  testMatchRequiresAllFields;   IO.println "  ✓ testMatchRequiresAllFields"
  testMultipleStale;            IO.println "  ✓ testMultipleStale"

end TestSuite.Shortcuts
