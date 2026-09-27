import Goudlokje.Report
import Goudlokje.Cli.Worksheets

/-!
# Results files

Reads the results files the linter writes (see `emitRecords`), and gets current results for
worksheets whose results file is missing or out of date.
-/

namespace Goudlokje.Cli

open Lean System

/-- The results of checking one module, read from its results file. -/
structure ModuleResults where
  /-- The hash of the source that was checked (see `sourceHash`). -/
  source       : UInt64 := 0
  /-- The hash of the `.test.json` it was checked against (see `expectationsHash`). -/
  expectations : UInt64 := 0
  /-- The exercises that were checked, with the names of the checks that ran on them. -/
  exercises    : Std.HashMap String (Array String) := {}
  /-- Exercises that could not be checked because of elaboration errors. -/
  skipped      : Std.HashSet String := {}
  findings     : Array Finding := #[]
  deriving Inhabited

/-- Adds the record `r` to the results. -/
def ModuleResults.add (acc : ModuleResults) : ResultRecord → ModuleResults
  | .header source expectations => { acc with source, expectations }
  | .exercise name checks => { acc with exercises := acc.exercises.insert name checks }
  | .skipped name => { acc with skipped := acc.skipped.insert name }
  | .finding f => { acc with findings := acc.findings.push f }

/-- Parses the lines of a results file into (source file, record) pairs. -/
def parseResultLines (contents : String) : Except String (Array (String × ResultRecord)) :=
  (contents.splitOn "\n").toArray.filterMapM fun line => do
    if line.trimAscii.isEmpty then return none
    let json ← Json.parse line
    return some (← json.getObjValAs? String "file", ← fromJson? json)

/-- The results in the results directory of the workspace in the current directory, by the real
    path of the worksheet. Results of files that no longer exist are left out. -/
def loadResults : IO (Std.HashMap FilePath ModuleResults) := do
  let dir := resultsDir (← IO.currentDir)
  unless ← dir.isDir do return {}
  let mut results := {}
  for entry in ← dir.readDir do
    if entry.path.extension != some "jsonl" then continue
    match parseResultLines (← IO.FS.readFile entry.path) with
    | .ok records =>
      for (file, record) in records do
        let some file ← try some <$> IO.FS.realPath file catch _ => pure none | continue
        results := results.insert file ((results.getD file {}).add record)
    | .error e => IO.eprintln s!"warning: ignoring results file {entry.path}: {e}"
  return results

/-- The results of `worksheet` among `results`, if they are for its current source. -/
def currentResults? (results : Std.HashMap FilePath ModuleResults) (worksheet : FilePath) :
    IO (Option ModuleResults) := do
  let some r := results[← IO.FS.realPath worksheet]? | return none
  if r.source != sourceHash (← IO.FS.readFile worksheet) then return none
  return some r

/-- The current results of the `worksheets`, after a build. A worksheet has no current results if
    its results file was deleted after it was built (or it was built elsewhere), or if it does not
    import Goudlokje. Those for which `needed` holds are elaborated again with `lake lean`, which
    writes new results without touching the build. Returns the results, and the output of
    elaborations that failed. -/
def getResults (worksheets : Array FilePath) (needed : FilePath → IO Bool) :
    IO (Array (Option ModuleResults) × Array (FilePath × IO.Process.Output)) := do
  let current ← worksheets.mapM (currentResults? (← loadResults))
  let missing ← (worksheets.zip current).filterMapM fun (w, r) => do
    return if r.isNone && (← needed w) then some w else none
  if missing.isEmpty then return (current, #[])
  let outputs ← parallelMap missing elaborate
  let results ← loadResults
  return (← worksheets.mapM (currentResults? results), (missing.zip outputs).filter (·.2.exitCode != 0))

end Goudlokje.Cli
