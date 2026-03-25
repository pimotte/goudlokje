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

end TestSuite.Check
