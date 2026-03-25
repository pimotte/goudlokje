import Goudlokje.Discovery

namespace TestSuite.Discovery

open Goudlokje

/-- `discoverWorksheets` given a single `.lean` path returns exactly one entry. -/
def testDiscoverSingleFile : IO Unit := do
  let entries ← discoverWorksheets #["TestSuite/Fixtures/Simple.lean"]
  unless entries.size == 1 do
    throw (IO.userError
      s!"testDiscoverSingleFile: expected 1, got {entries.size}")
  unless entries[0]!.sourcePath.toString == "TestSuite/Fixtures/Simple.lean" do
    throw (IO.userError
      s!"testDiscoverSingleFile: wrong path {entries[0]!.sourcePath}")

/-- `discoverWorksheets` given a directory discovers `.lean` files recursively. -/
def testDiscoverDirectory : IO Unit := do
  let entries ← discoverWorksheets #["TestSuite/Fixtures"]
  unless entries.size ≥ 1 do
    throw (IO.userError
      s!"testDiscoverDirectory: expected ≥1 entries, got {entries.size}")
  let names := entries.map (fun e => e.sourcePath.fileName)
  unless names.any (· == some "Simple.lean") do
    throw (IO.userError
      "testDiscoverDirectory: Simple.lean not found in discovery results")

/-- When a `.test.json` companion exists, `testPath` is populated. -/
def testDiscoverWithTestFile : IO Unit := do
  let dir : System.FilePath := "/tmp/goudlokje_disc_test"
  try IO.FS.createDir dir catch _ => pure ()
  let leanFile := dir / "Subject.lean"
  let jsonFile := dir / "Subject.test.json"
  IO.FS.writeFile leanFile "-- placeholder\n"
  IO.FS.writeFile jsonFile "{\"expected\": []}"
  let entries ← discoverWorksheets #[leanFile]
  try IO.FS.removeFile leanFile catch _ => pure ()
  try IO.FS.removeFile jsonFile catch _ => pure ()
  unless entries.size == 1 do
    throw (IO.userError
      s!"testDiscoverWithTestFile: expected 1, got {entries.size}")
  unless entries[0]!.testPath.isSome do
    throw (IO.userError
      "testDiscoverWithTestFile: expected testPath to be set")

/-- When no `.test.json` exists, `testPath` is `none`. -/
def testDiscoverWithoutTestFile : IO Unit := do
  let dir : System.FilePath := "/tmp/goudlokje_disc_notest"
  try IO.FS.createDir dir catch _ => pure ()
  let leanFile := dir / "Subject.lean"
  -- Make sure no stray json file is present.
  try IO.FS.removeFile (dir / "Subject.test.json") catch _ => pure ()
  IO.FS.writeFile leanFile "-- placeholder\n"
  let entries ← discoverWorksheets #[leanFile]
  try IO.FS.removeFile leanFile catch _ => pure ()
  unless entries.size == 1 do
    throw (IO.userError
      s!"testDiscoverWithoutTestFile: expected 1, got {entries.size}")
  unless entries[0]!.testPath.isNone do
    throw (IO.userError
      "testDiscoverWithoutTestFile: expected testPath to be none")

def runAll : IO Unit := do
  testDiscoverSingleFile;      IO.println "  ✓ testDiscoverSingleFile"
  testDiscoverDirectory;       IO.println "  ✓ testDiscoverDirectory"
  testDiscoverWithTestFile;    IO.println "  ✓ testDiscoverWithTestFile"
  testDiscoverWithoutTestFile; IO.println "  ✓ testDiscoverWithoutTestFile"

end TestSuite.Discovery
