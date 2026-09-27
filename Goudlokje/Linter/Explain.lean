import Goudlokje.Options
import Goudlokje.Steps
import Goudlokje.Scope
import Lean.Elab.Command
import Lean.Linter.Basic

/-!
# Explain linter

Debugging aid: with `linter.goudlokje.explain` enabled, reports for every command the exercise
name and the proof steps Goudlokje finds, numbered as in `.test.json` files. Steps are marked
`closes` if they close their goal, or
with the goal chain they belong to (`chain n`) if they are probe points; `input` marks steps in a
student input area.
-/

namespace Goudlokje

open Lean Elab Command

/-- Reports the steps of every command; see `linter.goudlokje.explain`. -/
def explainLinter : Linter where
  run := withSetOptionIn fun stx => do
    unless Linter.getLinterValue linter.goudlokje.explain (← Linter.getLinterOptions) do return
    let steps := collectSteps stx (← getInfoTrees)
    if steps.isEmpty then return
    let env ← getEnv
    let verbose := verboseModules (← getOptions)
    let fileMap ← getFileMap
    let chains := goalChains steps
    let mut lines := #[]
    for s in steps do
      let line := s.line fileMap
      let chain := chains.findIdx? (·.any (·.stx == s.stx))
      let flags :=
        (if s.isVerbose env verbose then ["verbose"] else []) ++
        (if ← inInputArea line then ["input"] else []) ++
        [chain.elim "closes" (s!"chain {·}")]
      lines := lines.push m!"step {stepNumber steps s}: {s.stx.getKind} [{", ".intercalate flags}]"
    Linter.logLint linter.goudlokje.explain stx
      m!"exercise {repr (exerciseName env verbose stx)}:{indentD (MessageData.joinSep lines.toList "\n")}"

initialize addLinter explainLinter

end Goudlokje
