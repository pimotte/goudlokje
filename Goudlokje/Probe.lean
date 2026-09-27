import Lean.Elab.Command
import Lean.Elab.Tactic.Basic
import Goudlokje.Steps
import Goudlokje.Options

/-!
# Probes

Runs a probe tactic on the goal of a proof step, in the context in which the step was elaborated.
Every probe gets its own heartbeat budget, so a probe that loops cannot hang the build, and the
messages a probe logs are discarded.
-/

namespace Goudlokje

open Lean Elab Command Meta Term

/-- A probe tactic, as configured and as parsed syntax. -/
structure Probe where
  name : String
  code : Syntax

/-- Parses the `;;`-separated probe tactics of `goudlokje.probes`. -/
def parseProbes (env : Environment) (probes : String) : Except String (Array Probe) :=
  (splitListOption probes).mapM fun name =>
    match Parser.runParserCategory env `tactic name with
    | .ok code => return { name, code }
    | .error e => throw s!"cannot parse probe tactic `{name}`: {e}"

/-- The result of running a probe on a goal. -/
inductive ProbeOutcome where
  /-- The probe closed the goal. -/
  | closed
  /-- The probe succeeded but left goals open. -/
  | progress
  /-- The probe failed. -/
  | failed
  /-- The probe ran out of heartbeats. -/
  | timeout
  deriving Repr, BEq, Inhabited

/-- Runs the tactic `code` on `goal` in `MetaM`, given the term elaboration context and state to
    run it in; returns the goals left open. -/
private def runTacticCode (goal : MVarId) (code : Syntax) (ctx : Term.Context) (s : Term.State) :
    MetaM (List MVarId) := do
  instantiateMVarDeclMVars goal
  let go : TermElabM (List MVarId) :=
    Term.withSynthesize do Tactic.run goal (Tactic.evalTactic code *> Tactic.pruneSolvedGoals)
  go.run' ctx s

/-- Runs `x` on a copy of `goal`, one of the goals before `step`, in the context in which the step
    was elaborated. (The original goal is already assigned by the step.) Messages that `x` logs are
    discarded. -/
def runOnGoal (step : Step) (goal : MVarId) (x : MVarId → MetaM α) : IO α := do
  let some decl := step.info.mctxBefore.findDecl? goal
    | throw (IO.userError "Goudlokje.runOnGoal: `goal` is not a goal before the step")
  step.ctx.runMetaM decl.lctx do
    -- Without the local instances, type class search would not see the hypotheses.
    Meta.withLocalInstances (decl.lctx.decls.toList.filterMap id) do
      let copy ← Meta.mkFreshExprSyntheticOpaqueMVar (← goal.getType)
      x copy.mvarId!

/-- Runs `probe` on `goal`, one of the goals before `step`, with a budget of `heartbeats`
    (in thousands, like `maxHeartbeats`). -/
def runProbe (step : Step) (goal : MVarId) (probe : Probe) (heartbeats : Nat) :
    CommandElabM ProbeOutcome := do
  let termCtx ← liftTermElabM read
  let termState ← liftTermElabM get
  -- `runMetaM` runs in a fresh `Core.Context` whose `maxHeartbeats` ignores the options, so the
  -- budget is set explicitly, counted from the start of the probe.
  runOnGoal step goal fun goal =>
    Core.withCurrHeartbeats <|
    withTheReader Core.Context ({ · with maxHeartbeats := heartbeats * 1000 }) do
      tryCatchRuntimeEx
        (do
          let goals ← runTacticCode goal probe.code termCtx termState
          return if goals.isEmpty then .closed else .progress)
        (fun e => return if e.isMaxHeartbeat then .timeout else .failed)

/-- Identifies a goal up to the names of its metavariables: its local context and target. -/
abbrev GoalFingerprint := Array (Name × Expr × Option Expr) × Expr

/-- The fingerprint of `goal` before `step`, or `none` if the goal still contains metavariables
    (then its meaning depends on their later assignment, so outcomes are not reused). -/
def goalFingerprint? (step : Step) (goal : MVarId) : CommandElabM (Option GoalFingerprint) := do
  let some decl := step.info.mctxBefore.findDecl? goal | return none
  let ctx := { step.ctx with mctx := step.info.mctxBefore }
  ctx.runMetaM decl.lctx do
    let target ← instantiateMVars decl.type
    let mut hyps := #[]
    for hyp in decl.lctx do
      if hyp.isImplementationDetail then continue
      let type ← instantiateMVars hyp.type
      let value ← hyp.value?.mapM instantiateMVars
      hyps := hyps.push (hyp.userName, type, value)
    if target.hasMVar || hyps.any fun (_, type, value) => type.hasMVar || value.any (·.hasMVar) then
      return none
    return some (hyps, target)

/-- Memoises probe outcomes per goal fingerprint and probe, within one command. -/
abbrev ProbeCache := Std.HashMap (GoalFingerprint × String) ProbeOutcome

/-- Runs `probe` on the main goal of `step`, reusing the outcome for an identical goal. -/
def runProbeCached (step : Step) (probe : Probe) (heartbeats : Nat) :
    StateT ProbeCache CommandElabM ProbeOutcome := do
  let some goal := step.mainGoal? | return .failed
  let key? := (← goalFingerprint? step goal).map (·, probe.name)
  if let some key := key? then
    if let some outcome := (← get)[key]? then return outcome
  let outcome ← runProbe step goal probe heartbeats
  if let some key := key? then modify (·.insert key outcome)
  return outcome

end Goudlokje
