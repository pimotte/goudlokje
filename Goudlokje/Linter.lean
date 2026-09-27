import Lean.Linter.Basic
import Goudlokje.Checks.Shortcut
import Goudlokje.Checks.Lint
import Goudlokje.Report

/-!
# The Goudlokje linter

Runs all enabled checks (`Check`) on every exercise and reports what they find. For each command
the exercise context (`getExercise?`) is computed once and shared by the checks.

Issues that the worksheet's `.test.json` lists as expected are not reported; issues it does not
list are reported with the check's severity (`Check.severity`); expectations that no longer match
an issue are reported as stale. On the command line, every checked exercise and every issue,
expected or not, is also written to the results file (see `emitRecords`) for `goudlokje check` and
`goudlokje update`. Commands with elaboration errors are not checked; for declarations among them a
`skipped` record is written, so that `update` keeps their expectations.
-/

namespace Goudlokje

open Lean Elab Command

/-- Runs `check` on `e`; `none` if the check could not run (e.g. no probes are configured). -/
private def runCheck (e : Exercise) : Check → CommandElabM (Option (Array Issue))
  | .shortcut => Checks.shortcuts e
  | .rawTactic => some <$> Checks.rawTactics e
  | .typeAscription => some <$> Checks.typeAscriptions e
  | .sorry => some <$> Checks.sorries e

/-- Drops issues reported at the same place for the same reason (a nested step is also part of
    the step around it). -/
private def dedup (issues : Array Issue) : Array Issue :=
  let key (i : Issue) := (i.check, i.ref.getPos?.map (·.byteIdx), i.tactic?)
  issues.foldl (init := #[]) fun acc i =>
    if acc.any (key · == key i) then acc else acc.push i

/-- Whether `.test.json` expects `issue` in `e`. -/
private def isExpected (e : Exercise) (issue : Issue) : Bool :=
  e.expectations.expects issue.check (e.stepNumber issue.step) issue.tactic?

/-- How to record an issue as expected, appended to the message of an unexpected issue. -/
private def hint : Check → MessageData
  | .shortcut | .typeAscription => m!"If this is intended, record it with `goudlokje update`."
  | .sorry => m!"If this exercise may contain `sorry`, allow it with `goudlokje update`."
  | .rawTactic =>
    m!"Tactics can be allowed for a whole project with the option `goudlokje.allowedTactics`."

/-- Reports the expectations of `e` that no longer hold, given the `results` of the checks. -/
private def reportStale (e : Exercise) (results : Array (Check × Array Issue)) :
    CommandElabM Unit := do
  let found := results.flatMap fun (check, issues) =>
    issues.map fun i => (check, e.stepNumber i.step, i.tactic?)
  let exercise := repr e.name
  for entry in e.expectations.stale (results.map (·.1)) found do
    let (check, severity, msg) : Check × MessageSeverity × MessageData := match entry with
      | .shortcut s => (.shortcut, .warning, m!"expected shortcut `{s.tactic}` at step {s.step} \
          of exercise {exercise} no longer occurs; remove it with `goudlokje update`")
      | .lint l true => ((Check.ofName? l.check).getD .rawTactic, .error, m!"`{l.check}` at \
          step {l.step} of exercise {exercise} cannot be recorded as expected; remove it with \
          `goudlokje update`")
      | .lint l false => ((Check.ofName? l.check).getD .typeAscription, .warning, m!"expected \
          `{l.check}` at step {l.step} of exercise {exercise} no longer occurs; remove it with \
          `goudlokje update`")
      | .allowSorry => (.sorry, .warning, m!"exercise {exercise} allows `sorry` but contains \
          none; remove `allowSorry` with `goudlokje update`")
    logFinding check.linterOption e.stx severity msg

/-- Reports the `issues` each check found in `e`; returns the records for the results file. -/
private def report (e : Exercise) (results : Array (Check × Array Issue)) :
    CommandElabM (Array ResultRecord) := do
  let mut records := #[.exercise e.name (results.map (·.1.name))]
  for (check, issues) in results do
    for issue in issues do
      unless isExpected e issue do
        logFinding check.linterOption issue.ref check.severity m!"{issue.message}\n\n{hint check}"
      let pos := e.fileMap.toPosition (issue.ref.getPos?.getD 0)
      records := records.push <| .finding {
        check, exercise := e.name, step := e.stepNumber issue.step
        line := pos.line, column := pos.column, tactic? := issue.tactic?
        message := ← issue.message.toString }
  reportStale e results
  return records

/-- The records for the results file of command `stx`, reporting what the checks find. -/
private def checkCommand (stx : Syntax) : CommandElabM (Array ResultRecord) := do
  let linterOptions ← Linter.getLinterOptions
  let enabled := Check.all.filter (Linter.getLinterValue ·.linterOption linterOptions)
  if enabled.isEmpty then return #[]
  if (← get).messages.hasErrors then
    let env ← getEnv
    let verbose := verboseModules (← getOptions)
    if isVerboseKind env verbose stx.getKind || stx.isOfKind ``Parser.Command.declaration then
      return #[.skipped (exerciseName env verbose stx)]
    return #[]
  let some e ← getExercise? stx | return #[]
  let mut results := #[]
  for check in enabled do
    if let some issues ← runCheck e check then
      results := results.push (check, dedup issues)
  report e results

/-- The Goudlokje linter; see the module documentation. -/
def goudlokjeLinter : Linter where
  run := withSetOptionIn fun stx => do
    -- Every command emits, so that the results file is started even without exercises.
    emitRecords (← checkCommand stx)

initialize addLinter goudlokjeLinter

end Goudlokje
