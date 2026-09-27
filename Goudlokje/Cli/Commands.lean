import Goudlokje.Cli.Worksheets
import Goudlokje.Cli.Changes

/-!
# `goudlokje check` and `goudlokje update`

Both work on worksheets: modules of a library in the current Lake workspace that import
`Goudlokje`. The checks themselves run as linters during `lake build`, which also writes their
results to the results files (see `emitRecords`).

* `check` builds the worksheets. Findings that `.test.json` does not expect are errors, so the
  build fails. Lake does not track `.test.json`, so for worksheets whose `.test.json` changed since
  they were built, the recorded results are compared with the current `.test.json` instead.
* `update` builds the worksheets and updates their `.test.json` files from the results: new
  findings are recorded as expected, stale expectations removed, after confirmation or, with
  `--all`, directly.

Neither rebuilds up-to-date worksheets: missing results are recomputed with `lake lean`, which
leaves the build state alone (by `check` only for worksheets with a `.test.json`).
-/

namespace Goudlokje.Cli

open System

/-- Prints the output of elaborations that failed. -/
private def printFailed (failed : Array (FilePath × IO.Process.Output)) : IO Unit :=
  for (_, out) in failed do IO.eprint (out.stdout ++ out.stderr)

/-- Compares the results `r` of `worksheet` with its current `.test.json`, printing what is
    unexpected or stale like the linter does; returns whether there are errors. -/
private def recheck (worksheet : FilePath) (r : ModuleResults) : IO Bool := do
  let expectations ← match ← loadExpectations (testJsonPath worksheet) with
    | .ok e => pure e
    | .error e => IO.eprintln s!"error: {e}"; return true
  IO.println s!"{worksheet}: .test.json changed since the worksheet was built, so the build \
    output above is out of date for it; comparing the recorded results with .test.json:"
  let mut problems := 0
  let mut errors := false
  for f in r.findings do
    unless (expectations.get f.exercise).expects f.check f.step f.tactic? do
      let severity := if f.check.severity == .error then "error" else "warning"
      IO.eprintln s!"{severity}: {worksheet}:{f.line}:{f.column}: {f.message}"
      problems := problems + 1
      errors := errors || f.check.severity == .error
  for change in proposeChanges expectations r do
    if change matches .recordShortcut .. | .recordLint .. | .allowSorry .. then continue
    let severity := if change.automatic then "error" else "warning"
    IO.eprintln s!"{severity}: {worksheet}: stale expectation: {change.describe}"
    problems := problems + 1
    errors := errors || change.automatic
  if problems == 0 then IO.println s!"{worksheet}: all findings are expected"
  return errors

/-- `goudlokje check`; returns the exit code. -/
def check (paths : Array FilePath) : IO UInt32 := do
  let worksheets ← findWorksheets paths
  if worksheets.isEmpty then
    IO.eprintln "No worksheets found."
    return 1
  let built ← build worksheets
  -- Without results, the build output is all there is; it can only be out of date if there is a
  -- `.test.json` that changed.
  let (results, failed) ← getResults worksheets fun w => (testJsonPath w).pathExists
  printFailed failed
  let mut errors := !failed.isEmpty
  for w in worksheets, r? in results do
    let some r := r? | continue
    -- The build checked `w` against the `.test.json` of that time.
    if r.expectations == (← expectationsHash (testJsonPath w)) then continue
    errors := (← recheck w r) || errors
  return if built && !errors then 0 else 1

/-- Asks a yes/no question on the terminal; the default is no. -/
private def confirm (question : String) : IO Bool := do
  IO.print s!"{question}? [y/N] "
  (← IO.getStdout).flush
  let answer ← (← IO.getStdin).getLine
  return answer.trimAscii.toString.toLower == "y"

/-- Updates the `.test.json` of worksheet `source` according to `results`. -/
private def updateWorksheet (source : FilePath) (results : ModuleResults) (all : Bool) :
    IO Unit := do
  let path := testJsonPath source
  let old ← match ← loadExpectations path with
    | .ok old => pure old
    | .error e =>
      IO.eprintln s!"error: {e}; not updating it (fix or delete the file first)"
      return
  for name in results.skipped do
    IO.eprintln s!"warning: {source}: exercise {name.quote} has errors; its expectations are kept"
  let mut new := old
  for change in proposeChanges old results do
    if change.automatic || all then
      IO.println s!"{source}: {change.describe}."
      new := change.apply new
    else if ← confirm s!"{source}: {change.describe}" then
      new := change.apply new
  if Lean.toJson new == Lean.toJson old then return
  if new.exercises.isEmpty then
    if ← path.pathExists then IO.FS.removeFile path
  else
    saveExpectations path new

/-- `goudlokje update`; returns the exit code. -/
def update (paths : Array FilePath) (all : Bool) : IO UInt32 := do
  let worksheets ← findWorksheets paths
  if worksheets.isEmpty then
    IO.eprintln "No worksheets found."
    return 1
  IO.println s!"Checking {worksheets.size} worksheet(s)..."
  -- Unexpected findings are errors, so the build is expected to fail; its output is only shown
  -- for worksheets that could not be checked.
  let out ← lakeOutput (#["build"] ++ worksheets.map toString)
  let (results, failed) ← getResults worksheets fun _ => pure true
  let mut shownOutput := false
  for w in worksheets, r? in results do
    match r? with
    | some r => updateWorksheet w r all
    | none =>
      -- No results: the worksheet does not import Goudlokje or does not elaborate. Only worth
      -- mentioning if there are expectations that are now not updated.
      unless ← (testJsonPath w).pathExists do continue
      if !shownOutput then
        shownOutput := true
        if out.exitCode != 0 then IO.eprint (out.stdout ++ out.stderr)
        printFailed failed
      IO.eprintln s!"warning: {w}: no exercises were checked; its .test.json is kept"
  return 0

end Goudlokje.Cli
