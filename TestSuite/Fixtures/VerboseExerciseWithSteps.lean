-- Fixture: combined Verbose Lean proof wrapper (Exercise block) with full Lean Verbose
-- step syntax (`Let's first/now prove that …`) inside the proof body.
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
--   - `show 1+1=2` → first non-boundary tactic of step 1; NOT last → SHORTCUT
--   - `norm_num` → 2nd tactic in step 1; suppressed by filterVerboseSteps
--   - Step boundary `Let's now prove that 2+2=4` → used as step marker; not emitted
--   - `show 2+2=4` → first non-boundary tactic of step 2; last overall → skip-last
--   - `norm_num` → 2nd tactic in step 2; suppressed by filterVerboseSteps
-- Expected: 1 shortcut (show at step 1)
import Verbose.English.All
open Verbose English

set_option linter.unusedTactic false

Exercise "test exercise with step boundaries"
  Given: (dummy : Nat)
  Assume: (h : dummy = dummy)
  Conclusion: 1 + 1 = 2 ∧ 2 + 2 = 4
Proof:
  Let's first prove that 1 + 1 = 2
  show 1 + 1 = 2  -- SHORTCUT: first non-boundary tactic of step 1; `decide` closes it; not last
  norm_num        -- 2nd tactic in step 1; suppressed by filterVerboseSteps
  Let's now prove that 2 + 2 = 4
  show 2 + 2 = 4  -- first non-boundary tactic of step 2; last overall → dropped by skip-last
  norm_num        -- 2nd tactic in step 2; suppressed by filterVerboseSteps
QED
