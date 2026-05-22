import Goudlokje.Config
import Lean.Data.Json

namespace TestSuite.Config

open Goudlokje

private def assertEq [BEq α] [Repr α] (expected actual : α) (msg : String) : IO Unit :=
  unless expected == actual do
    throw (IO.userError s!"{msg}: expected {repr expected}, got {repr actual}")

def testValidConfig : IO Unit := do
  let json ← IO.ofExcept (Lean.Json.parse "{\"tactics\": [\"ring\", \"omega\"]}")
  let cfg ← IO.ofExcept (Lean.fromJson? (α := Config) json)
  assertEq #["ring", "omega"] cfg.tactics "testValidConfig"

def testEmptyTactics : IO Unit := do
  let json ← IO.ofExcept (Lean.Json.parse "{\"tactics\": []}")
  let cfg ← IO.ofExcept (Lean.fromJson? (α := Config) json)
  assertEq #[] cfg.tactics "testEmptyTactics"

def testMissingTacticsField : IO Unit := do
  let json ← IO.ofExcept (Lean.Json.parse "{}")
  match Lean.fromJson? (α := Config) json with
  | .ok _  => throw (IO.userError "testMissingTacticsField: expected failure but got success")
  | .error _ => pure ()

def testUnknownFieldsIgnored : IO Unit := do
  let json ← IO.ofExcept (Lean.Json.parse "{\"tactics\": [\"ring\"], \"extra\": 42}")
  let cfg ← IO.ofExcept (Lean.fromJson? (α := Config) json)
  assertEq #["ring"] cfg.tactics "testUnknownFieldsIgnored"

def testRoundTrip : IO Unit := do
  let original : Config := { tactics := #["simp", "ring", "omega"] }
  let json := Lean.toJson original
  let parsed ← IO.ofExcept (Lean.fromJson? json)
  assertEq original parsed "testRoundTrip"

def runAll : IO Unit := do
  testValidConfig;     IO.println "  ✓ testValidConfig"
  testEmptyTactics;    IO.println "  ✓ testEmptyTactics"
  testMissingTacticsField;
                        IO.println "  ✓ testMissingTacticsField"
  testUnknownFieldsIgnored;
                        IO.println "  ✓ testUnknownFieldsIgnored"
  testRoundTrip;       IO.println "  ✓ testRoundTrip"

end TestSuite.Config
