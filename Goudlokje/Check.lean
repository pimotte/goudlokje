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

private def checkWorksheet
    (ws : WorksheetEntry) (cfg : Config)
    (debugMode : Bool) (verbose : Bool) : IO WorksheetCheckSummary := do
  let analyzed ← analyzeFileIsolated ws.sourcePath cfg.tactics cfg.filterVerboseSteps debugMode verbose
  let found := analyzed.results
  let tf := TestFile.load (ws.testPath.getD (ws.sourcePath.withExtension "test.json"))
  let cr := classify found (← tf)
  let unexpectedCount := cr.shortcuts.foldl (fun acc shortcut =>
    match shortcut with
    | .unexpected _ => acc + 1
    | .expected _ => acc) 0
  return {
    probeResultCount := found.size
    probeAttempts := analyzed.probeAttempts
    shortcuts := cr.shortcuts
    stale := cr.stale
    unexpectedCount := unexpectedCount
  }

/-- Run check mode: analyse worksheets and report any unexpected shortcuts.
    Returns the number of unexpected shortcuts found (non-zero → CI failure).
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
    unexpectedCount := unexpectedCount + summary.unexpectedCount
  return unexpectedCount

end Goudlokje
