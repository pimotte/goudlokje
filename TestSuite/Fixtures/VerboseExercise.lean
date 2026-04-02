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
-- The proof below has NO Verbose step boundaries (no `Let's first prove that …`),
-- so `filterVerboseSteps` does NOT suppress the wrapper.
--
-- Expected result with `decide` probe and NO filterVerboseSteps:
--   - Without fix: 2 shortcuts (wrapper@Proof: + show@step1; norm_num is last → skip)
--   - With fix:    1 shortcut  (show@step1 only)
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
