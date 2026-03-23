import Goudlokje.Config
import Goudlokje.Discovery
import Goudlokje.Analysis
import Goudlokje.TestFile
import Goudlokje.Shortcuts

namespace Goudlokje

/-- Prompt the user for a yes/no answer. Returns true for 'y'/'Y'. -/
private def promptYN (prompt : String) : IO Bool := do
  IO.print prompt
  let line ← (← IO.getStdin).getLine
  return line.trimAscii.toString.toLower == "y"

/-- Run update mode: interactively (or with --all) accept shortcuts and persist them.
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
  let cache ← mkEnvCache
  for ws in worksheets do
    IO.println s!"Updating {ws.sourcePath}..."
    -- Count every probe attempt (success or failure) so we can warn when nothing is probed.
    let probeAttempts ← IO.mkRef (0 : Nat)
    let probeLog : Option (Nat → Nat → String → Bool → IO Unit) :=
      if debugMode then
        some fun line col tactic succeeded => do
          probeAttempts.modify (· + 1)
          if verbose then
            let mark := if succeeded then "✓" else "✗"
            IO.println s!"  Probe {mark} {line}:{col} — `{tactic}`"
      else none
    let found ← analyzeFile ws.sourcePath cfg.tactics cfg.filterVerboseSteps (some cache) probeLog
    let testPath := ws.testPath.getD (ws.sourcePath.withExtension "test.json")
    let tf    ← TestFile.load testPath
    let cr    := classify found tf
    if debugMode then
      IO.println s!"  Found {found.size} probe result(s), {cr.shortcuts.size} shortcut(s), {cr.stale.size} stale entry/entries"
      let attempts ← probeAttempts.get
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

    let newTf : TestFile := { expected := newExpected }
    newTf.save testPath

end Goudlokje
