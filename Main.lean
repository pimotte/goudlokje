import Cli
import Goudlokje.Config
import Goudlokje.Check

open Cli

private def loadConfig (debug : Bool) : IO Goudlokje.Config := do
  let path : System.FilePath := ".goudlokje.json"
  if ← path.pathExists then
    if debug then
      IO.println s!"[debug] Loading config from {path}"
    Goudlokje.Config.load path
  else
    if debug then
      IO.println s!"[debug] No config file found at {path}, using defaults (no tactics)"
    return { tactics := #[] }

private def runCheck (p : Parsed) : IO UInt32 := do
  let verbose := p.hasFlag "verbose"
  let debug   := p.hasFlag "debug" || verbose
  let cfg ← loadConfig debug
  let rawPaths := p.variableArgsAs! String
  let paths : Array System.FilePath :=
    if rawPaths.isEmpty then #[⟨"."⟩] else rawPaths.map (⟨·⟩)
  let n ← Goudlokje.runCheck paths cfg debug verbose
  return if n == 0 then 0 else 1

private def checkCmd : Cmd := `[Cli|
  check VIA runCheck;
  "Check Lean worksheets for unexpected shortcuts."

  FLAGS:
    debug;   "Print debug information during analysis (probe counts, result statistics)"
    verbose; "Print all debug information plus detailed per-file probe hits"

  ARGS:
    ...files : String; "Lean files or directories to check (default: current directory)"
]

private def goudlokjeCmd : Cmd := `[Cli|
  goudlokje NOOP;
  "Worksheet shortcut checker for Lean 4 exercises."

  SUBCOMMANDS:
    checkCmd
]

def main (args : List String) : IO UInt32 :=
  goudlokjeCmd.validate args
