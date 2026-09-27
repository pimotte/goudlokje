import Cli
import Goudlokje.Cli.Commands

open Cli

private def paths (p : Parsed) : Array System.FilePath :=
  let raw := p.variableArgsAs! String
  if raw.isEmpty then #["."] else raw.map (⟨·⟩)

private def runCheck (p : Parsed) : IO UInt32 :=
  Goudlokje.Cli.check (paths p)

private def runUpdate (p : Parsed) : IO UInt32 :=
  Goudlokje.Cli.update (paths p) (all := p.hasFlag "all")

private def checkCmd : Cmd := `[Cli|
  check VIA runCheck;
  "Build the worksheets and fail on findings their .test.json does not expect."

  ARGS:
    ...paths : String; "Worksheets or directories (default: the current directory)"
]

private def updateCmd : Cmd := `[Cli|
  update VIA runUpdate;
  "Record new findings as expected and remove stale expectations in .test.json files."

  FLAGS:
    all; "Make all changes without asking"

  ARGS:
    ...paths : String; "Worksheets or directories (default: the current directory)"
]

private def goudlokjeCmd : Cmd := `[Cli|
  goudlokje NOOP;
  "Checks Lean Verbose worksheets for shortcuts and style issues."

  SUBCOMMANDS:
    checkCmd;
    updateCmd
]

def main (args : List String) : IO UInt32 :=
  goudlokjeCmd.validate args
