import Lean.Data.Json
import Lean.Data.Json.FromToJson
import Goudlokje.Analysis

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
    (filterVerboseSteps : Bool := false)
    (debug : Bool := false) (verbose : Bool := false) : IO ProbeWorkerResult := do
  let debugMode := debug || verbose
  let appPath ← IO.appPath
  let proc ← IO.Process.output {
    cmd := appPath.toString
    args := #["__probe_file__", filePath.toString,
      boolArg filterVerboseSteps, boolArg debugMode, boolArg verbose] ++ probeTactics
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
  | fileArg :: filterArg :: debugArg :: verboseArg :: tacticArgs =>
    let filePath : System.FilePath := fileArg
    let filterVerboseSteps := parseBoolArg filterArg
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
    let results ← analyzeFile filePath tacticArgs.toArray filterVerboseSteps (onProbe := probeLog)
    let payload : ProbeWorkerResult := {
      results := results
      probeAttempts := ← probeAttempts.get
    }
    IO.println probeWorkerSentinel
    IO.println (Lean.toJson payload).compress
    pure 0
  | _ =>
    IO.eprintln "usage: __probe_file__ <file> <filterVerboseSteps> <debug> <verbose> [tactic ...]"
    pure 2

end Goudlokje
