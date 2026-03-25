-- Fixture for testing that the Lean Verbose `Exercise`/`Example` command's proof
-- wrapper is NOT probed by Goudlokje.
--
-- The `mkExercise` elaboration expands to:
--   example <objs ++ hyps>... : <concl> :=
--     by with(out)_suggestions%$tkp <proof>; done
-- where `tkp` is the `Proof:` token.  This gives the `with(out)_suggestions`
-- wrapper tactic a source position pointing at `Proof:`, and goalsBefore equal
-- to the exercise conclusion — so a probe tactic that closes the goal would
-- fire here as a false positive.
--
-- Exercise 1 (plain Lean, no step boundaries): show at line 28 is a shortcut;
--   norm_num at line 29 is last → skip.  1 shortcut.
-- Exercise 2 (combined: Exercise wrapper + step boundaries + `We compute` phrase):
--   `We compute` at step 1 (line 41) is a shortcut; step 2 `We compute` (line 43) is last → skip.
--   1 shortcut.
-- Total with `decide` probe: 2 shortcuts.
import Verbose.English.All
open Verbose English

set_option linter.unusedTactic false

Exercise "test exercise without step boundaries"
  Given: (dummy : Nat)
  Assume: (h : 0 = 0)
  Conclusion: 1 + 1 = 2
Proof:
  show 1 + 1 = 2   -- noop; `decide` can close the goal here (not the last step → shortcut)
  norm_num          -- closes the goal; `decide` works here too but it is last → skip
QED

-- Exercise 2: combined Exercise wrapper, step boundaries, and Lean Verbose phrase proof.
-- Verifies that `isSyntheticTacticContainer` filters the wrapper and `We compute`
-- (a full Lean Verbose phrase) is correctly detected as a shortcut at the first non-last step.
Exercise "test exercise with step boundaries and Lean Verbose phrase proof"
  Given: (dummy : Nat)
  Assume: (h : dummy = dummy)
  Conclusion: 1 + 1 = 2 ∧ 2 + 2 = 4
Proof:
  Let's first prove that 1 + 1 = 2
  We compute  -- SHORTCUT: full Lean Verbose phrase; `decide` closes `1+1=2`; not last
  Let's now prove that 2 + 2 = 4
  We compute  -- Lean Verbose phrase; last overall → dropped by skip-last
QED
