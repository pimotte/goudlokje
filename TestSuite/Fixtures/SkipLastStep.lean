-- Fixture for testing that shortcuts at the last tactic position are not reported.
-- Uses a Verbose 2-step proof so that after filterVerboseSteps the tactic positions
-- are exactly 2 (one representative per step), making the skip-last rule observable.
-- `decide` can close the goal at both positions, but the last (step 2) must be skipped.
-- Before fix: 2 shortcuts (one per step). After fix: 1 shortcut (step 2 is last → skip).
-- This reproduces the mwe/WaterproofExercisesLean exercise 1.1.13 issue:
-- a probe tactic that works at the final step does not save any proof lines.
import Verbose.English.All

set_option linter.unusedTactic false

example : 1 + 1 = 2 ∧ 2 + 2 = 4 := by
  Let's first prove that 1 + 1 = 2
  norm_num   -- step 1: goal is 1+1=2; decide closes it (shortcut, not last after filter)
  Let's now prove that 2 + 2 = 4
  norm_num   -- step 2: goal is 2+2=4; decide closes it (last after filter → skip)
