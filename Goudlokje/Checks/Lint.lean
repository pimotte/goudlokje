import Goudlokje.Exercise
import Goudlokje.Finding
import Goudlokje.SyntaxUtil

/-!
# Lint checks

Style checks on the steps of Verbose exercises in student input areas, all based on the syntax
the student wrote:

* `rawTactics` (B1): raw Lean tactics instead of Verbose tactics.
* `typeAscriptions` (B2): type annotations, `(e : T)` and `Fix x : T`.
* `sorries` (B3): `sorry` and `admit`.
-/

namespace Goudlokje.Checks

open Lean Elab Command

/-- Tactic kinds for `sorry` and `admit`. -/
private def sorryTacticKinds : Array SyntaxNodeKind :=
  #[``Lean.Parser.Tactic.tacticSorry, `Lean.Parser.Tactic.tacticAdmit]

/-- B1: steps using a raw Lean tactic, unless its leading token is allowed by
    `goudlokje.allowedTactics`. `sorry` and `admit` are left to `sorries`. -/
def rawTactics (e : Exercise) : CommandElabM (Array Issue) := do
  let env ← getEnv
  let allowed := splitListOption (goudlokje.allowedTactics.get (← getOptions))
  return e.inputSteps.filterMap fun step => do
    guard <| !e.isVerbose env step && !sorryTacticKinds.contains step.stx.getKind
    let token := (leadingToken? step.stx).getD "?"
    guard <| !allowed.contains token
    return {
      check := .rawTactic, step, ref := step.stx
      message := m!"raw Lean tactic `{token}` at step {e.stepNumber step} of exercise \
        {repr e.name}; use a Lean Verbose tactic instead" }

/-- Whether `kind` is a Verbose `Fix` tactic (its parser is declared in a `Verbose.*.Fix`
    module, in any language). -/
private def isFixKind (env : Environment) (kind : SyntaxNodeKind) : Bool :=
  match kindModule? env kind with
  | some (.str (.str `Verbose _) "Fix") => true
  | _ => false

/-- B2: type ascriptions `(e : T)` in steps, and `Fix` steps with a typed binder. -/
def typeAscriptions (e : Exercise) : CommandElabM (Array Issue) := do
  let env ← getEnv
  let mut issues : Array Issue := #[]
  for step in e.inputSteps do
    for ascription in findAllOfKind step.stx ``Parser.Term.typeAscription do
      issues := issues.push {
        check := .typeAscription, step, ref := ascription
        message := m!"type annotation `{ascription}` at step {e.stepNumber step} of exercise \
          {repr e.name}" }
    if isFixKind env step.stx.getKind && hasAtom step.stx ":" then
      issues := issues.push {
        check := .typeAscription, step, ref := step.stx
        message := m!"`Fix` with a type annotation at step {e.stepNumber step} of exercise \
          {repr e.name}" }
  return issues

/-- B3: `sorry` and `admit`, as tactics or as terms inside a step. -/
def sorries (e : Exercise) : CommandElabM (Array Issue) := do
  let mut issues : Array Issue := #[]
  for step in e.inputSteps do
    let refs :=
      if sorryTacticKinds.contains step.stx.getKind then #[step.stx]
      else findAllOfKind step.stx ``Parser.Term.sorry
    for ref in refs do
      issues := issues.push {
        check := .sorry, step, ref
        message := m!"`sorry` at step {e.stepNumber step} of exercise {repr e.name}" }
  return issues

end Goudlokje.Checks
