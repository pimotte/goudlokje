import Goudlokje.Config
import Goudlokje.Discovery
import Goudlokje.Analysis
import Goudlokje.ProbeWorker
import Goudlokje.TestFile
import Goudlokje.Shortcuts
import Goudlokje.Lint

namespace Goudlokje

private structure WorksheetCheckSummary where
  probeResultCount : Nat
  probeAttempts    : Nat
  shortcuts        : Array ShortcutResult
  stale            : Array StaleEntry
  unexpectedCount  : Nat
  lintResult       : LintClassificationResult

private def checkWorksheet
    (ws : WorksheetEntry) (cfg : Config)
    (debugMode : Bool) (verbose : Bool) : IO WorksheetCheckSummary := do
  let analyzed ← analyzeFileIsolated ws.sourcePath cfg.tactics cfg.filterVerboseSteps debugMode verbose
  let found := analyzed.results
  let testPath := ws.testPath.getD (ws.sourcePath.withExtension "test.json")
  let tf := TestFile.load testPath
  let cr := classify found (← tf)
  let unexpectedCount := cr.shortcuts.foldl (fun acc shortcut =>
    match shortcut with
    | .unexpected _ => acc + 1
    | .expected _ => acc) 0
  -- Run lint checks in an isolated subprocess to avoid accumulating memory.
  let lintFound ← lintFileIsolated ws.sourcePath
  let lintCr := classifyLint lintFound (← tf)
  return {
    probeResultCount := found.size
    probeAttempts := analyzed.probeAttempts
    shortcuts := cr.shortcuts
    stale := cr.stale
    unexpectedCount := unexpectedCount
    lintResult := lintCr
  }

/-- Run check mode: analyse worksheets and report any unexpected shortcuts or lint violations.
    Returns the number of unexpected shortcuts + undocumented B3 lint errors (non-zero → CI failure).
    When `debug` is true, prints analysis statistics per file.
    When `verbose` is true, implies `debug` and additionally lists all discovered
    worksheets upfront and logs every individual probe hit per file. -/
def runCheck
    (paths : Array System.FilePath) (cfg : Config)
    (debug : Bool := false) (verbose : Bool := false) : IO Nat := do
  let worksheets ← discoverWorksheets paths
  let debugMode := debug || verbose
  if verbose then
    IO.println s!"Discovered {worksheets.size} worksheet(s):"
    for ws in worksheets do
      IO.println s!"  {ws.sourcePath}"
  if debugMode then
    IO.println s!"Probing with {cfg.tactics.size} tactic(s): {", ".intercalate cfg.tactics.toList}"
  let mut unexpectedCount := 0
  for ws in worksheets do
    IO.println s!"Checking {ws.sourcePath}..."
    let summary ← checkWorksheet ws cfg debugMode verbose
    if debugMode then
      IO.println s!"  Found {summary.probeResultCount} probe result(s), {summary.shortcuts.size} shortcut(s), {summary.stale.size} stale entry/entries"
      if summary.probeAttempts == 0 && !cfg.tactics.isEmpty then
        IO.println s!"  Warning: no tactic positions found in {ws.sourcePath} — verify all imports are available (run via `lake exe goudlokje`)"
    for r in summary.shortcuts do
      printShortcutResult r
    for s in summary.stale do
      printStaleEntry s
    -- Report lint results.
    for v in summary.lintResult.violations do
      printLintViolationResult v
    for s in summary.lintResult.stale do
      printStaleLintEntry s
    unexpectedCount := unexpectedCount + summary.unexpectedCount
    -- Count B1 and B3 lint violations as build failures.
    -- B1 always fails the build (cannot be suppressed); B3 (sorry) is always an error.
    unexpectedCount := unexpectedCount + summary.lintResult.violations.foldl (fun acc v =>
      match v with
      | .unexpected r => if r.check == "B1" || r.check == "B3" then acc + 1 else acc
      | .expected _ => acc) 0
  return unexpectedCount

end Goudlokje
