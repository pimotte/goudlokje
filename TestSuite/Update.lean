import Goudlokje.Update
import Goudlokje.Config
import Goudlokje.TestFile

namespace TestSuite.Update

open Goudlokje

/-- Set up a temporary workspace containing a single `.lean` file.
    Returns the file path and the expected `.test.json` path. -/
private def setupTempWorkspace (dir : System.FilePath) : IO (System.FilePath × System.FilePath) := do
  try IO.FS.createDir dir catch _ => pure ()
  let leanFile := dir / "Fixture.lean"
  -- A Verbose two-step proof so that `decide` finds shortcuts at `show` positions.
  -- Issue #13: shortcuts are only detected in Verbose Lean proofs.
  IO.FS.writeFile leanFile
    ("import Verbose.English.All\n" ++
     "example : 1 + 1 = 2 ∧ 2 + 2 = 4 := by\n" ++
     "  Let's first prove that 1 + 1 = 2\n" ++
     "  show 1 + 1 = 2\n" ++
     "  norm_num\n" ++
     "  Let's now prove that 2 + 2 = 4\n" ++
     "  show 2 + 2 = 4\n" ++
     "  norm_num\n")
  let testJson := dir / "Fixture.test.json"
  -- Ensure any leftover from a previous run is removed.
  try IO.FS.removeFile testJson catch _ => pure ()
  return (leanFile, testJson)

/-- `runUpdate --all` must write a `.test.json` listing every found shortcut. -/
def testUpdateAllCreatesTestFile : IO Unit := do
  let dir : System.FilePath := "/tmp/goudlokje_update_create"
  let (leanFile, testJson) ← setupTempWorkspace dir
  let cfg : Config := { tactics := #["decide"] }
  runUpdate #[leanFile] cfg true
  unless ← testJson.pathExists do
    throw (IO.userError "testUpdateAllCreates: .test.json was not created")
  let tf ← TestFile.load testJson
  unless tf.expected.size ≥ 1 do
    throw (IO.userError
      s!"testUpdateAllCreates: expected ≥1 entries in test file, got {tf.expected.size}")

/-- `runUpdate --all` on a file that already has a `.test.json` must merge
    new shortcuts and not duplicate existing ones. -/
def testUpdateAllIdempotent : IO Unit := do
  let dir : System.FilePath := "/tmp/goudlokje_update_idem"
  let (leanFile, testJson) ← setupTempWorkspace dir
  let cfg : Config := { tactics := #["decide"] }
  -- First pass: write the test file.
  runUpdate #[leanFile] cfg true
  let tf1 ← TestFile.load testJson
  -- Second pass: should not add duplicates.
  runUpdate #[leanFile] cfg true
  let tf2 ← TestFile.load testJson
  unless tf1.expected.size == tf2.expected.size do
    throw (IO.userError
      s!"testUpdateAllIdempotent: size changed from {tf1.expected.size} to {tf2.expected.size}")

/-- `runUpdate --all` with no tactics writes an empty `.test.json`. -/
def testUpdateAllNoTactics : IO Unit := do
  let dir : System.FilePath := "/tmp/goudlokje_update_notactics"
  let (leanFile, testJson) ← setupTempWorkspace dir
  let cfg : Config := { tactics := #[] }
  runUpdate #[leanFile] cfg true
  unless ← testJson.pathExists do
    throw (IO.userError "testUpdateAllNoTactics: .test.json was not created")
  let tf ← TestFile.load testJson
  unless tf.expected.size == 0 do
    throw (IO.userError
      s!"testUpdateAllNoTactics: expected 0 entries, got {tf.expected.size}")

/-- `runUpdate` with debug=true must still create the test file correctly. -/
def testUpdateDebugMode : IO Unit := do
  let dir : System.FilePath := "/tmp/goudlokje_update_debug"
  let (leanFile, testJson) ← setupTempWorkspace dir
  let cfg : Config := { tactics := #["decide"] }
  runUpdate #[leanFile] cfg true (debug := true)
  unless ← testJson.pathExists do
    throw (IO.userError "testUpdateDebugMode: .test.json was not created")
  let tf ← TestFile.load testJson
  unless tf.expected.size ≥ 1 do
    throw (IO.userError
      s!"testUpdateDebugMode: expected ≥1 entries in test file, got {tf.expected.size}")

/-- `runUpdate` with verbose=true must still create the test file correctly. -/
def testUpdateVerboseMode : IO Unit := do
  let dir : System.FilePath := "/tmp/goudlokje_update_verbose"
  let (leanFile, testJson) ← setupTempWorkspace dir
  let cfg : Config := { tactics := #["decide"] }
  runUpdate #[leanFile] cfg true (verbose := true)
  unless ← testJson.pathExists do
    throw (IO.userError "testUpdateVerboseMode: .test.json was not created")
  let tf ← TestFile.load testJson
  unless tf.expected.size ≥ 1 do
    throw (IO.userError
      s!"testUpdateVerboseMode: expected ≥1 entries in test file, got {tf.expected.size}")

/-- `runUpdate` must not throw when a file has an unresolvable import.
    It should log the error and continue. In debug mode it also emits
    a diagnostic warning about missing tactic positions. -/
def testUpdateGracefulOnImportError : IO Unit := do
  let dir : System.FilePath := "/tmp/goudlokje_update_badimport"
  try IO.FS.createDirAll dir catch _ => pure ()
  let leanFile := dir / "Bad.lean"
  IO.FS.writeFile leanFile "import SomethingThatDoesNotExist\nexample : 1 + 1 = 2 := by rfl\n"
  let testJson := dir / "Bad.test.json"
  try IO.FS.removeFile testJson catch _ => pure ()
  let cfg : Config := { tactics := #["decide"] }
  -- Non-debug mode: should not throw.
  runUpdate #[leanFile] cfg true
  -- Debug mode: should also complete without throwing (and will emit the warning).
  runUpdate #[leanFile] cfg true (debug := true)

def runAll : IO Unit := do
  testUpdateAllCreatesTestFile
  IO.println "  ✓ testUpdateAllCreatesTestFile"
  testUpdateAllIdempotent
  IO.println "  ✓ testUpdateAllIdempotent"
  testUpdateAllNoTactics
  IO.println "  ✓ testUpdateAllNoTactics"
  testUpdateDebugMode
  IO.println "  ✓ testUpdateDebugMode"
  testUpdateVerboseMode
  IO.println "  ✓ testUpdateVerboseMode"
  testUpdateGracefulOnImportError
  IO.println "  ✓ testUpdateGracefulOnImportError"

end TestSuite.Update
