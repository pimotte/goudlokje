-- Fixture: combined Verbose Lean proof wrapper (Exercise block) with full Lean Verbose
-- step syntax (`Let's first/now prove that …`) and Lean Verbose proof phrases
-- (`We compute`) inside the proof body.
--
-- The Exercise block expands to:
--   example <vars>... : <concl> := by with(out)_suggestions%$tkp <proof>; done
-- where the `with(out)_suggestions` wrapper at `Proof:` is filtered by
-- `isSyntheticTacticContainer` (always active, no configuration needed).
-- The step boundaries inside the proof are handled by `filterVerboseSteps`.
--
-- Tactic positions and their fate with `decide` probe + `filterVerboseSteps := true`:
--   - `with(out)_suggestions` at `Proof:` → filtered (isSyntheticTacticContainer)
--   - Step boundary `Let's first prove that 1+1=2` → used as step marker; not emitted
--   - `We compute` (step 1) → first non-boundary tactic; NOT last → SHORTCUT (decide closes 1+1=2)
--   - Step boundary `Let's now prove that 2+2=4` → used as step marker; not emitted
--   - `We compute` (step 2) → first non-boundary tactic; last overall → skip-last
-- Expected: 1 shortcut (`We compute` at step 1, line 29)
import Verbose.English.All
open Verbose English

set_option linter.unusedTactic false

Exercise "test exercise with step boundaries"
  Given: (dummy : Nat)
  Assume: (h : dummy = dummy)
  Conclusion: 1 + 1 = 2 ∧ 2 + 2 = 4
Proof:
  Let's first prove that 1 + 1 = 2
  We compute  -- SHORTCUT: full Lean Verbose phrase; `decide` closes `1+1=2`; not last
  Let's now prove that 2 + 2 = 4
  We compute  -- full Lean Verbose phrase; last overall → dropped by skip-last
QED
