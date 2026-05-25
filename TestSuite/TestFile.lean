import Goudlokje.TestFile
import Lean.Data.Json

namespace TestSuite.TestFile

open Goudlokje

private def assertEq [BEq α] [Repr α] (expected actual : α) (msg : String) : IO Unit :=
  unless expected == actual do
    throw (IO.userError s!"{msg}: expected {repr expected}, got {repr actual}")

def testRoundTripEmpty : IO Unit := do
  let original : TestFile := { expected := #[] }
  let parsed ← IO.ofExcept (Lean.fromJson? (Lean.toJson original))
  assertEq original parsed "testRoundTripEmpty"

def testRoundTripSingle : IO Unit := do
  let original : TestFile := {
    expected := #[{ exercise := "foo", stepNumber := 1, tacticIndexInStep := 2, tactic := "ring" }]
  }
  let parsed ← IO.ofExcept (Lean.fromJson? (Lean.toJson original))
  assertEq original parsed "testRoundTripSingle"

def testRoundTripMultiple : IO Unit := do
  let original : TestFile := {
    expected := #[
      { exercise := "exercise_1", stepNumber := 1,  tacticIndexInStep := 1, tactic := "ring" },
      { exercise := "exercise_2", stepNumber := 3,  tacticIndexInStep := 2, tactic := "omega" }
    ]
  }
  let parsed ← IO.ofExcept (Lean.fromJson? (Lean.toJson original))
  assertEq original parsed "testRoundTripMultiple"

def testParseJson : IO Unit := do
  let raw := "{\"expected\":[{\"exercise\":\"ex1\",\"stepNumber\":2,\"tacticIndexInStep\":3,\"tactic\":\"simp\"}]}"
  let json ← IO.ofExcept (Lean.Json.parse raw)
  let tf ← IO.ofExcept (Lean.fromJson? (α := TestFile) json)
  assertEq 1       tf.expected.size                  "testParseJson: size"
  assertEq "ex1"   tf.expected[0]!.exercise           "testParseJson: exercise"
  assertEq 2       tf.expected[0]!.stepNumber         "testParseJson: stepNumber"
  assertEq 3       tf.expected[0]!.tacticIndexInStep  "testParseJson: tacticIndexInStep"
  assertEq "simp"  tf.expected[0]!.tactic             "testParseJson: tactic"

def testLoadMissingFileReturnsEmpty : IO Unit := do
  let tf ← TestFile.load "/tmp/goudlokje_test_does_not_exist_abc123.test.json"
  assertEq 0 tf.expected.size "testLoadMissingFileReturnsEmpty"
  assertEq 0 tf.lint.size     "testLoadMissingFileReturnsEmpty: lint"

def testRoundTripLint : IO Unit := do
  let original : TestFile := {
    expected := #[]
    lint := #[{ file := "a.lean", line := 5, column := 3, check := "B1", message := "Raw tactic" }]
  }
  let parsed ← IO.ofExcept (Lean.fromJson? (Lean.toJson original))
  assertEq original parsed "testRoundTripLint"

def testParseJsonNoLintField : IO Unit := do
  -- "lint" field is optional — should default to empty array.
  let raw := "{\"expected\":[]}"
  let json ← IO.ofExcept (Lean.Json.parse raw)
  let tf ← IO.ofExcept (Lean.fromJson? (α := TestFile) json)
  assertEq 0 tf.lint.size "testParseJsonNoLintField"

def runAll : IO Unit := do
  testRoundTripEmpty;              IO.println "  ✓ testRoundTripEmpty"
  testRoundTripSingle;             IO.println "  ✓ testRoundTripSingle"
  testRoundTripMultiple;           IO.println "  ✓ testRoundTripMultiple"
  testParseJson;                   IO.println "  ✓ testParseJson"
  testLoadMissingFileReturnsEmpty; IO.println "  ✓ testLoadMissingFileReturnsEmpty"
  testRoundTripLint;               IO.println "  ✓ testRoundTripLint"
  testParseJsonNoLintField;        IO.println "  ✓ testParseJsonNoLintField"

end TestSuite.TestFile
