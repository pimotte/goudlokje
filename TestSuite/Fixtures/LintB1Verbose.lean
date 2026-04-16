-- Fixture for CheckB1 false-positive regression tests.
-- Verbose lines beginning with "Let's" or "Since" must NOT be reported as B1
-- violations, even though they expand internally to raw Lean tactics.
import Verbose.English.All

set_option linter.unusedTactic false

-- "Let's first/now prove that" are Verbose step boundaries; they expand
-- internally to raw tactics but must not be flagged by B1.
example : 1 + 1 = 2 ∧ 2 + 2 = 4 := by
  Let's first prove that 1 + 1 = 2
  norm_num
  Let's now prove that 2 + 2 = 4
  norm_num

-- "Let's prove that k works" opens an existential Verbose step; must not flag.
example : ∃ k : ℕ, 4 = 2 * k := by
  Let's prove that 2 works
  rfl
