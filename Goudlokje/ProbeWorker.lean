import Lean.Data.Json
import Lean.Data.Json.FromToJson
import Goudlokje.Analysis
import Goudlokje.TestFile
import Goudlokje.Lint

namespace Goudlokje

structure ProbeWorkerResult where
  results : Array ProbeResult
  probeAttempts : Nat
  deriving Repr, Inhabited, Lean.ToJson, Lean.FromJson

def probeWorkerSentinel : String := "__GOUDLOKJE_PROBE_RESULT__"

private def boolArg (value : Bool) : String :=
  if value then "true" else "false"

private def parseBoolArg (value : String) : Bool :=
  value.trimAscii.toString.toLower == "true"

private def parseProbeWorkerOutput (stdout : String) : IO (String × ProbeWorkerResult) := do
  match stdout.splitOn (probeWorkerSentinel ++ "\n") with
  | [logs, jsonText] =>
    let json ← IO.ofExcept <| Lean.Json.parse jsonText.trimAscii.toString
    let payload ← IO.ofExcept <| Lean.fromJson? json
    pure (logs, payload)
  | _ =>
    throw <| IO.userError "probe worker did not return a parseable payload"

def analyzeFileIsolated
    (filePath : System.FilePath) (probeTactics : Array String)
    (debug : Bool := false) (verbose : Bool := false) : IO ProbeWorkerResult := do
  let debugMode := debug || verbose
  let appPath ← IO.appPath
  let proc ← IO.Process.output {
    cmd := appPath.toString
    args := #["__probe_file__", filePath.toString, boolArg debugMode, boolArg verbose] ++ probeTactics
  }
  unless proc.stderr.isEmpty do
    IO.eprint proc.stderr
  unless proc.exitCode == 0 do
    if !proc.stdout.isEmpty then
      IO.print proc.stdout
    throw <| IO.userError s!"probe worker failed for {filePath} with exit code {proc.exitCode}"
  let (logs, payload) ← parseProbeWorkerOutput proc.stdout
  unless logs.isEmpty do
    IO.print logs
  pure payload

def runProbeWorkerCli (args : List String) : IO UInt32 := do
  match args with
  | fileArg :: debugArg :: verboseArg :: tacticArgs =>
    let filePath : System.FilePath := fileArg
    let debugMode := parseBoolArg debugArg
    let verbose := parseBoolArg verboseArg
    let probeAttempts ← IO.mkRef (0 : Nat)
    let probeLog : Option (Nat → Nat → String → Bool → IO Unit) :=
      if debugMode then
        some fun line col tactic succeeded => do
          probeAttempts.modify (· + 1)
          if verbose then
            let mark := if succeeded then "✓" else "✗"
            IO.println s!"  Probe {mark} {line}:{col} — `{tactic}`"
      else none
    let results ← analyzeFile filePath tacticArgs.toArray (onProbe := probeLog) (verbose := verbose)
    let payload : ProbeWorkerResult := {
      results := results
      probeAttempts := ← probeAttempts.get
    }
    IO.println probeWorkerSentinel
    IO.println (Lean.toJson payload).compress
    pure 0
  | _ =>
    IO.eprintln "usage: __probe_file__ <file> <debug> <verbose> [tactic ...]"
    pure 2

-- ============================================================
-- Lint worker: runs lintFile in an isolated subprocess
-- ============================================================

def lintWorkerSentinel : String := "__GOUDLOKJE_LINT_RESULT__"

structure LintWorkerResult where
  results : Array LintResult
  deriving Repr, Inhabited, Lean.ToJson, Lean.FromJson

private def parseLintWorkerOutput (stdout : String) : IO (String × LintWorkerResult) := do
  match stdout.splitOn (lintWorkerSentinel ++ "\n") with
  | [logs, jsonText] =>
    let json ← IO.ofExcept <| Lean.Json.parse jsonText.trimAscii.toString
    let payload ← IO.ofExcept <| Lean.fromJson? json
    pure (logs, payload)
  | _ =>
    throw <| IO.userError "lint worker did not return a parseable payload"

def lintFileIsolated (filePath : System.FilePath) : IO (Array LintResult) := do
  let appPath ← IO.appPath
  let proc ← IO.Process.output {
    cmd  := appPath.toString
    args := #["__lint_file__", filePath.toString]
  }
  unless proc.stderr.isEmpty do
    IO.eprint proc.stderr
  unless proc.exitCode == 0 do
    if !proc.stdout.isEmpty then
      IO.print proc.stdout
    throw <| IO.userError s!"lint worker failed for {filePath} with exit code {proc.exitCode}"
  let (logs, payload) ← parseLintWorkerOutput proc.stdout
  unless logs.isEmpty do
    IO.print logs
  pure payload.results

def runLintWorkerCli (args : List String) : IO UInt32 := do
  match args with
  | [fileArg] =>
    let filePath : System.FilePath := fileArg
    let results ← lintFile filePath none
    let payload : LintWorkerResult := { results }
    IO.println lintWorkerSentinel
    IO.println (Lean.toJson payload).compress
    pure 0
  | _ =>
    IO.eprintln "usage: __lint_file__ <file>"
    pure 2

end Goudlokje
