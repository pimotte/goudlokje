import FixtureDeps
import TestSuite.Config
import TestSuite.TestFile
import TestSuite.Shortcuts
import TestSuite.Discovery
import TestSuite.Analysis
import TestSuite.Check
import TestSuite.Update

-- Dispatch for lightweight suites: run all tests in-process.
private def runSuiteInProcess (name : String) : IO UInt32 := do
  match name with
  | "Config"    => TestSuite.Config.runAll;    return 0
  | "TestFile"  => TestSuite.TestFile.runAll;  return 0
  | "Shortcuts" => TestSuite.Shortcuts.runAll; return 0
  | "Discovery" => TestSuite.Discovery.runAll; return 0
  | other       => IO.eprintln s!"unknown suite: {other}"; return 2

-- Dispatch for integration tests: run a single named test in-process.
-- Each integration test runs in its own subprocess (spawned by the orchestrator
-- below), so that Lean elaboration memory is freed between tests.
private def runTestInProcess (suite testName : String) : IO UInt32 := do
  match suite, testName with
  | "Analysis", "testDetectsDecideShortcut" =>
    TestSuite.Analysis.testDetectsDecideShortcut; return 0
  | "Analysis", "testNoTacticsNoResults" =>
    TestSuite.Analysis.testNoTacticsNoResults; return 0
  | "Analysis", "testNoDuplicateResults" =>
    TestSuite.Analysis.testNoDuplicateResults; return 0
  | "Analysis", "testDetectsDecideShortcutInVerboseFile" =>
    TestSuite.Analysis.testDetectsDecideShortcutInVerboseFile; return 0
  | "Analysis", "testDetectsDecideShortcutInWaterproofFile" =>
    TestSuite.Analysis.testDetectsDecideShortcutInWaterproofFile; return 0
  | "Analysis", "testDetectsDecideShortcutInVerboseWaterproofFile" =>
    TestSuite.Analysis.testDetectsDecideShortcutInVerboseWaterproofFile; return 0
  | "Analysis", "testVerboseFilterReducesResults" =>
    TestSuite.Analysis.testVerboseFilterReducesResults; return 0
  | "Analysis", "testVerboseFilterKeepsFirstPerStep" =>
    TestSuite.Analysis.testVerboseFilterKeepsFirstPerStep; return 0
  | "Analysis", "testVerboseFilterRespectsDeclarationBoundaries" =>
    TestSuite.Analysis.testVerboseFilterRespectsDeclarationBoundaries; return 0
  | "Analysis", "testOnProbeCallbackInvoked" =>
    TestSuite.Analysis.testOnProbeCallbackInvoked; return 0
  | "Analysis", "testOnProbeCallbackIncludesFailures" =>
    TestSuite.Analysis.testOnProbeCallbackIncludesFailures; return 0
  | "Analysis", "testOnProbeSuccessCountMatchesResults" =>
    TestSuite.Analysis.testOnProbeSuccessCountMatchesResults; return 0
  | "Analysis", "testSkipLastTacticNotReported" =>
    TestSuite.Analysis.testSkipLastTacticNotReported; return 0
  | "Analysis", "testVerboseExerciseDoesNotProbeBeforeProof" =>
    TestSuite.Analysis.testVerboseExerciseDoesNotProbeBeforeProof; return 0
  | "Analysis", "testBulletSeenAsStepInVerboseWaterproofFull" =>
    TestSuite.Analysis.testBulletSeenAsStepInVerboseWaterproofFull; return 0
  | "Check", "testCheckNonZeroForUnexpectedShortcuts" =>
    TestSuite.Check.testCheckNonZeroForUnexpectedShortcuts; return 0
  | "Check", "testCheckZeroWithEmptyTactics" =>
    TestSuite.Check.testCheckZeroWithEmptyTactics; return 0
  | "Check", "testCheckDebugMode" =>
    TestSuite.Check.testCheckDebugMode; return 0
  | "Check", "testCheckVerboseMode" =>
    TestSuite.Check.testCheckVerboseMode; return 0
  | "Check", "testCheckGracefulOnImportError" =>
    TestSuite.Check.testCheckGracefulOnImportError; return 0
  | "Update", "testUpdateAllCreatesTestFile" =>
    TestSuite.Update.testUpdateAllCreatesTestFile; return 0
  | "Update", "testUpdateAllIdempotent" =>
    TestSuite.Update.testUpdateAllIdempotent; return 0
  | "Update", "testUpdateAllNoTactics" =>
    TestSuite.Update.testUpdateAllNoTactics; return 0
  | "Update", "testUpdateDebugMode" =>
    TestSuite.Update.testUpdateDebugMode; return 0
  | "Update", "testUpdateVerboseMode" =>
    TestSuite.Update.testUpdateVerboseMode; return 0
  | "Update", "testUpdateGracefulOnImportError" =>
    TestSuite.Update.testUpdateGracefulOnImportError; return 0
  | _, _ =>
    IO.eprintln s!"unknown test: {suite}/{testName}"; return 2

-- Spawn a lightweight suite as a single subprocess.
private def spawnSuite (appPath : System.FilePath) (name label : String) : IO Bool := do
  IO.println s!"=== {label} ==="
  let proc ← IO.Process.output {
    cmd  := appPath.toString
    args := #["__run_suite__", name]
  }
  IO.print proc.stdout
  unless proc.stderr.isEmpty do IO.eprint proc.stderr
  return proc.exitCode == 0

private structure IntTestSpec where
  suite : String
  name  : String

-- Spawn each integration test as its own subprocess so that the Lean
-- elaboration environment (and its memory) is discarded after each test.
private def spawnIntegrationSuite
    (appPath : System.FilePath) (label : String) (tests : Array IntTestSpec) : IO Bool := do
  IO.println s!"=== {label} ==="
  let mut allPassed := true
  for t in tests do
    let proc ← IO.Process.output {
      cmd  := appPath.toString
      args := #["__run_test__", t.suite, t.name]
    }
    IO.print proc.stdout
    unless proc.stderr.isEmpty do IO.eprint proc.stderr
    if proc.exitCode == 0 then
      IO.println s!"  ✓ {t.name}"
    else
      IO.println s!"  ✗ {t.name}"
      allPassed := false
  return allPassed

private def analysisTests : Array IntTestSpec := #[
  { suite := "Analysis", name := "testDetectsDecideShortcut" },
  { suite := "Analysis", name := "testNoTacticsNoResults" },
  { suite := "Analysis", name := "testNoDuplicateResults" },
  { suite := "Analysis", name := "testDetectsDecideShortcutInVerboseFile" },
  { suite := "Analysis", name := "testDetectsDecideShortcutInWaterproofFile" },
  { suite := "Analysis", name := "testDetectsDecideShortcutInVerboseWaterproofFile" },
  { suite := "Analysis", name := "testVerboseFilterReducesResults" },
  { suite := "Analysis", name := "testVerboseFilterKeepsFirstPerStep" },
  { suite := "Analysis", name := "testVerboseFilterRespectsDeclarationBoundaries" },
  { suite := "Analysis", name := "testOnProbeCallbackInvoked" },
  { suite := "Analysis", name := "testOnProbeCallbackIncludesFailures" },
  { suite := "Analysis", name := "testOnProbeSuccessCountMatchesResults" },
  { suite := "Analysis", name := "testSkipLastTacticNotReported" },
  { suite := "Analysis", name := "testVerboseExerciseDoesNotProbeBeforeProof" },
  { suite := "Analysis", name := "testBulletSeenAsStepInVerboseWaterproofFull" },
]

private def checkTests : Array IntTestSpec := #[
  { suite := "Check", name := "testCheckNonZeroForUnexpectedShortcuts" },
  { suite := "Check", name := "testCheckZeroWithEmptyTactics" },
  { suite := "Check", name := "testCheckDebugMode" },
  { suite := "Check", name := "testCheckVerboseMode" },
  { suite := "Check", name := "testCheckGracefulOnImportError" },
]

private def updateTests : Array IntTestSpec := #[
  { suite := "Update", name := "testUpdateAllCreatesTestFile" },
  { suite := "Update", name := "testUpdateAllIdempotent" },
  { suite := "Update", name := "testUpdateAllNoTactics" },
  { suite := "Update", name := "testUpdateDebugMode" },
  { suite := "Update", name := "testUpdateVerboseMode" },
  { suite := "Update", name := "testUpdateGracefulOnImportError" },
]

def main (args : List String) : IO UInt32 := do
  -- Internal dispatch: called by subprocesses spawned below.
  match args with
  | ["__run_suite__", name]        => return (← runSuiteInProcess name)
  | ["__run_test__", suite, tname] => return (← runTestInProcess suite tname)
  -- analyzeFileIsolated (used by runCheck / runUpdate) spawns the current binary
  -- with __probe_file__ args.  Handle that here so it doesn't fall through to
  -- the orchestrator and cause an exponential process explosion.
  | "__probe_file__" :: rest       => return (← Goudlokje.runProbeWorkerCli rest)
  | _ => pure ()
  -- Orchestrator: run each suite / test in its own subprocess.
  let appPath ← IO.appPath
  let mut anyFailed := false
  for (name, label) in #[("Config",    "Config tests"),
                          ("TestFile",  "TestFile tests"),
                          ("Shortcuts", "Shortcuts tests"),
                          ("Discovery", "Discovery tests")] do
    unless ← spawnSuite appPath name label do anyFailed := true
    IO.println ""
  for (label, tests) in #[("Analysis integration tests", analysisTests),
                           ("Check end-to-end tests",     checkTests),
                           ("Update end-to-end tests",    updateTests)] do
    unless ← spawnIntegrationSuite appPath label tests do anyFailed := true
    IO.println ""
  if anyFailed then
    IO.println "Some tests FAILED."
    return 1
  else
    IO.println "All tests passed."
    return 0
