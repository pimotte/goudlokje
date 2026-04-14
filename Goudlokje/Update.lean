import Goudlokje.Config
import Goudlokje.Discovery
import Goudlokje.Analysis
import Goudlokje.ProbeWorker
import Goudlokje.TestFile
import Goudlokje.Shortcuts
import Goudlokje.Lint

namespace Goudlokje

/-- Prompt the user for a yes/no answer. Returns true for 'y'/'Y'. -/
private def promptYN (prompt : String) : IO Bool := do
  IO.print prompt
  let line ← (← IO.getStdin).getLine
  return line.trimAscii.toString.toLower == "y"

/-- Run update mode: interactively (or with --all) accept shortcuts and lint violations,
    and persist them to the test file.
    Stale entries are removed (with confirmation in interactive mode, automatic in --all).
    When `debug` is true, prints analysis statistics per file.
    When `verbose` is true, implies `debug` and additionally lists all discovered
    worksheets upfront and logs every individual probe hit per file. -/
def runUpdate
    (paths : Array System.FilePath) (cfg : Config) (acceptAll : Bool)
    (debug : Bool := false) (verbose : Bool := false) : IO Unit := do
  let worksheets ← discoverWorksheets paths
  let debugMode := debug || verbose
  if verbose then
    IO.println s!"Discovered {worksheets.size} worksheet(s):"
    for ws in worksheets do
      IO.println s!"  {ws.sourcePath}"
  if debugMode then
    IO.println s!"Probing with {cfg.tactics.size} tactic(s): {", ".intercalate cfg.tactics.toList}"
  let envCache ← mkEnvCache
  for ws in worksheets do
    IO.println s!"Updating {ws.sourcePath}..."
    let analyzed ← analyzeFileIsolated ws.sourcePath cfg.tactics cfg.filterVerboseSteps debugMode verbose
    let found := analyzed.results
    let testPath := ws.testPath.getD (ws.sourcePath.withExtension "test.json")
    let tf    ← TestFile.load testPath
    let cr    := classify found tf
    if debugMode then
      IO.println s!"  Found {found.size} probe result(s), {cr.shortcuts.size} shortcut(s), {cr.stale.size} stale entry/entries"
      let attempts := analyzed.probeAttempts
      if attempts == 0 && !cfg.tactics.isEmpty then
        IO.println s!"  Warning: no tactic positions found in {ws.sourcePath} — verify all imports are available (run via `lake exe goudlokje`)"

    let mut newExpected := tf.expected

    -- Handle unexpected shortcuts: prompt user (or auto-accept with --all).
    for r in cr.shortcuts do
      if let .unexpected p := r then
        let accept ← do
          if acceptAll then
            IO.println s!"Accepting shortcut at {p.file}:{p.line}:{p.column} — `{p.tactic}`"
            pure true
          else
            promptYN s!"Shortcut at {p.file}:{p.line}:{p.column} — `{p.tactic}`. Accept? [y/N] "
        if accept then
          newExpected := newExpected.push {
            file   := p.file
            line   := p.line
            column := p.column
            tactic := p.tactic
          }

    -- Handle stale entries: prompt user (or auto-remove with --all).
    for s in cr.stale do
      let remove ← do
        if acceptAll then
          IO.println s!"Removing stale entry {s.entry.file}:{s.entry.line}:{s.entry.column} — `{s.entry.tactic}`"
          pure true
        else
          promptYN s!"Stale entry at {s.entry.file}:{s.entry.line}:{s.entry.column} — `{s.entry.tactic}`. Remove? [y/N] "
      if remove then
        newExpected := newExpected.filter (· != s.entry)

    -- Run lint checks and classify against the current test file, sharing the env cache.
    let lintFound ← lintFile ws.sourcePath (some envCache)
    let lintCr := classifyLint lintFound tf
    let mut newLint := tf.lint

    -- Handle unexpected lint violations: prompt user (or auto-accept with --all).
    for v in lintCr.violations do
      if let .unexpected r := v then
        let accept ← do
          if acceptAll then
            IO.println s!"Accepting lint [{r.check}] at {r.file}:{r.line}:{r.column} — {r.message}"
            pure true
          else
            promptYN s!"Lint [{r.check}] at {r.file}:{r.line}:{r.column} — {r.message}. Accept? [y/N] "
        if accept then
          newLint := newLint.push {
            file    := r.file
            line    := r.line
            column  := r.column
            check   := r.check
            message := r.message
          }

    -- Handle stale lint entries: prompt user (or auto-remove with --all).
    for s in lintCr.stale do
      let remove ← do
        if acceptAll then
          IO.println s!"Removing stale lint entry [{s.entry.check}] {s.entry.file}:{s.entry.line}:{s.entry.column}"
          pure true
        else
          promptYN s!"Stale lint [{s.entry.check}] at {s.entry.file}:{s.entry.line}:{s.entry.column}. Remove? [y/N] "
      if remove then
        newLint := newLint.filter fun e =>
          !(e.file == s.entry.file && e.line == s.entry.line &&
            e.column == s.entry.column && e.check == s.entry.check)

    let newTf : TestFile := { expected := newExpected, lint := newLint }
    newTf.save testPath

end Goudlokje
