import Goudlokje.Check
import Goudlokje.Config

namespace TestSuite.Check

open Goudlokje

/-- End-to-end: `runCheck` must return > 0 when unexpected shortcuts exist.
    `Simple.lean` has no `.test.json`, so all found shortcuts are unexpected. -/
def testCheckNonZeroForUnexpectedShortcuts : IO Unit := do
  let cfg : Config := { tactics := #["decide"] }
  let n ← runCheck #["TestSuite/Fixtures/Simple.lean"] cfg
  unless n > 0 do
    throw (IO.userError
      s!"testCheckNonZero: expected >0 unexpected shortcuts, got {n}")

/-- End-to-end: `runCheck` must return 0 when no tactics are configured. -/
def testCheckZeroWithEmptyTactics : IO Unit := do
  let cfg : Config := { tactics := #[] }
  let n ← runCheck #["TestSuite/Fixtures/Simple.lean"] cfg
  unless n == 0 do
    throw (IO.userError
      s!"testCheckZero: expected 0 with empty tactics, got {n}")

/-- `runCheck` with debug=true must still return the correct non-zero count. -/
def testCheckDebugMode : IO Unit := do
  let cfg : Config := { tactics := #["decide"] }
  let n ← runCheck #["TestSuite/Fixtures/Simple.lean"] cfg (debug := true)
  unless n > 0 do
    throw (IO.userError
      s!"testCheckDebugMode: expected >0 unexpected shortcuts, got {n}")

/-- `runCheck` with verbose=true must still return the correct non-zero count. -/
def testCheckVerboseMode : IO Unit := do
  let cfg : Config := { tactics := #["decide"] }
  let n ← runCheck #["TestSuite/Fixtures/Simple.lean"] cfg (verbose := true)
  unless n > 0 do
    throw (IO.userError
      s!"testCheckVerboseMode: expected >0 unexpected shortcuts, got {n}")

/-- `runCheck` must not throw when a file has an unresolvable import.
    It should log the error and continue, returning 0 unexpected shortcuts.
    In debug mode it also emits a diagnostic warning about missing tactic positions. -/
def testCheckGracefulOnImportError : IO Unit := do
  let dir : System.FilePath := "/tmp/goudlokje_check_badimport"
  try IO.FS.createDirAll dir catch _ => pure ()
  let leanFile := dir / "Bad.lean"
  IO.FS.writeFile leanFile "import SomethingThatDoesNotExist\nexample : 1 + 1 = 2 := by rfl\n"
  let cfg : Config := { tactics := #["decide"] }
  -- Non-debug mode: should not throw; returns 0 shortcuts.
  let n ← runCheck #[leanFile] cfg
  unless n == 0 do
    throw (IO.userError
      s!"testCheckGracefulOnImportError: expected 0 shortcuts (on error), got {n}")
  -- Debug mode: should also complete without throwing (and will emit the warning).
  let n2 ← runCheck #[leanFile] cfg (debug := true)
  unless n2 == 0 do
    throw (IO.userError
      s!"testCheckGracefulOnImportError (debug): expected 0 shortcuts, got {n2}")

/-- Integration test: `runCheck` on VerboseWaterproofFull.lean with the tactic
    "Since p, q and r we conclude that p ∧ q ∧ r" must return exactly 1 unexpected
    shortcut.  The fixture has 2 Verbose steps (lines 19–20); skip-last removes
    the final step (line 20), leaving exactly the step at line 19 where the goal
    is still `p ∧ q ∧ r` and the probe tactic closes it directly. -/
def testCheckVerboseWaterproofFullExactlyOneShortcut : IO Unit := do
  let tactic := "Since p, q and r we conclude that p ∧ q ∧ r"
  let cfg : Config := { tactics := #[tactic] }
  let n ← runCheck #["TestSuite/Fixtures/VerboseWaterproofFull.lean"] cfg
  unless n == 1 do
    throw (IO.userError
      s!"testCheckVerboseWaterproofFull: expected exactly 1 unexpected shortcut, got {n}")
  -- Also verify position: the single shortcut must be at line 19.
  let results ← analyzeFile "TestSuite/Fixtures/VerboseWaterproofFull.lean" #[tactic]
  unless results.size == 1 do
    throw (IO.userError
      s!"testCheckVerboseWaterproofFull (position): expected 1 probe result, got {results.size}")
  unless results[0]!.line == 19 do
    throw (IO.userError
      s!"testCheckVerboseWaterproofFull (position): expected shortcut at line 19, \
        got line {results[0]!.line}")

/-- Integration test: `runCheck` on LintB3.lean (which has an undocumented `sorry`)
    must return > 0 because B3 (sorry) is an error-level lint violation.
    This verifies that lint results are counted in the runCheck exit code
    and that the EnvCache is correctly threaded through the check workflow. -/
def testCheckCountsB3LintViolation : IO Unit := do
  let cfg : Config := { tactics := #[] }
  let n ← runCheck #["TestSuite/Fixtures/LintB3.lean"] cfg
  unless n > 0 do
    throw (IO.userError
      s!"testCheckCountsB3LintViolation: expected >0 (B3 sorry counts as error), got {n}")

def runAll : IO Unit := do
  testCheckNonZeroForUnexpectedShortcuts;
    IO.println "  ✓ testCheckNonZeroForUnexpectedShortcuts"
  testCheckZeroWithEmptyTactics;
    IO.println "  ✓ testCheckZeroWithEmptyTactics"
  testCheckDebugMode;
    IO.println "  ✓ testCheckDebugMode"
  testCheckVerboseMode;
    IO.println "  ✓ testCheckVerboseMode"
  testCheckGracefulOnImportError;
    IO.println "  ✓ testCheckGracefulOnImportError"
  testCheckVerboseWaterproofFullExactlyOneShortcut;
    IO.println "  ✓ testCheckVerboseWaterproofFullExactlyOneShortcut"
  testCheckCountsB3LintViolation;
    IO.println "  ✓ testCheckCountsB3LintViolation"

end TestSuite.Check
