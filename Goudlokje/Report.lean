import Lean.Linter.Init
import Lean.Data.Json
import Lean.Elab.Command
import Std.Sync.Mutex
import Goudlokje.Check
import Goudlokje.Expectations

/-!
# Reporting

How linters report findings: as messages in the editor and build output, and, when a worksheet is
checked on the command line (by `lake build` or `lake lean`), as JSON lines in its *results file*
`.lake/goudlokje/<module>.jsonl`, relative to the directory Lake runs in (the workspace root).

The results file is written anew every time the module is elaborated. Its first record holds
hashes of the source and of the `.test.json` it was checked against, so that `goudlokje check` and
`goudlokje update` can tell whether the results are still current without rebuilding anything.
-/

namespace Goudlokje

open Lean Elab

/-- Logs `msg` at `stx` as a message of the linter `linterOption`, with the given severity.
    Like `Lean.Linter.logLint` (so the message is recognised and persisted as a linter message),
    but findings that must fail the build can be errors. -/
def logFinding [Monad m] [MonadLog m] [AddMessageContext m] [MonadOptions m]
    (linterOption : Lean.Option Bool) (stx : Syntax) (severity : MessageSeverity)
    (msg : MessageData) : m Unit :=
  let disable := .note m!"This linter can be disabled with `set_option {linterOption.name} false`"
  logAt stx (.tagged linterOption.name <| .tagged Linter.linterMessageTag m!"{msg}{disable}")
    severity

/-- A finding, as recorded in the results file. -/
structure Finding where
  check    : Check
  exercise : String
  step     : Nat
  line     : Nat
  column   : Nat
  /-- For shortcuts: the probe tactic that closes the goal. -/
  tactic?  : Option String := none
  message  : String
  deriving Repr, BEq, Inhabited, ToJson, FromJson

/-- A record in the results file. -/
inductive ResultRecord where
  /-- The first record: hashes of the source (see `sourceHash`) and of the `.test.json` (see
      `expectationsHash`) that the results are for. -/
  | header (source expectations : UInt64)
  /-- An exercise that was checked by the checks named `checks`, so `update` knows which
      exercises still exist and which expectations could have been confirmed. -/
  | exercise (name : String) (checks : Array String)
  /-- A command that could not be checked because it has errors; `update` keeps its
      expectations. -/
  | skipped (name : String)
  | finding (finding : Finding)
  deriving Repr, BEq

instance : ToJson ResultRecord where
  toJson
    | .header source expectations =>
      Json.mkObj [("source", toJson source), ("expectations", toJson expectations)]
    | .exercise name checks => Json.mkObj [("exercise", name), ("checks", toJson checks)]
    | .skipped name => Json.mkObj [("skipped", name)]
    | .finding finding => Json.mkObj [("finding", toJson finding)]

instance : FromJson ResultRecord where
  fromJson? json :=
    (return .header (← json.getObjValAs? UInt64 "source")
      (← json.getObjValAs? UInt64 "expectations")) <|>
    (return .exercise (← json.getObjValAs? String "exercise")
      (← json.getObjValAs? (Array String) "checks")) <|>
    (return .skipped (← json.getObjValAs? String "skipped")) <|>
    (return .finding (← json.getObjValAs? Finding "finding"))

/-- A hash of a worksheet's source, as Lean reads it. -/
def sourceHash (source : String) : UInt64 :=
  hash source.crlfToLf

/-- The directory with the results files, relative to the workspace root `root`. -/
def resultsDir (root : System.FilePath) : System.FilePath :=
  root / ".lake" / "goudlokje"

/-- Whether the results file of this process's module has been started (see `emitRecord`). -/
private initialize resultsStarted : Std.Mutex Bool ← Std.Mutex.new false

/-- Appends `records` to the results file of the module being elaborated. The first call in an
    elaboration starts the file anew with a `header` record, so every command must call this, even
    without records. Only on the command line: the language server re-elaborates files while they
    are edited. -/
def emitRecords (records : Array ResultRecord) : Command.CommandElabM Unit := do
  unless internal.cmdlineSnapshots.get (← getOptions) do return
  let dir := resultsDir (← IO.currentDir)
  let path := dir / s!"{← getMainModule}.jsonl"
  let file ← getFileName
  let line (r : ResultRecord) := ((toJson r).setObjVal! "file" file).compress ++ "\n"
  let source := sourceHash (← getFileMap).source
  resultsStarted.atomically do
    unless ← get do
      let expectations ← expectationsHash (testJsonPath file)
      IO.FS.createDirAll dir
      IO.FS.writeFile path (line (.header source expectations))
      set true
    unless records.isEmpty do
      let handle ← IO.FS.Handle.mk path .append
      handle.putStr (String.join (records.map line).toList)

end Goudlokje
