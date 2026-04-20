-- Fixture for CheckB1: raw tactics inside a Verbose Lean proof should be flagged.
-- The Verbose step boundaries (Let's first prove that / Let's now prove that) make
-- this a Verbose proof. Raw tactics like constructor and exact should be flagged by B1.
import Verbose.English.All

set_option linter.unusedTactic false

-- Verbose proof with raw Lean tactics inside.
-- B1 should flag 'constructor' and subsequent 'exact' tactics.
example : 1 = 1 ∧ 2 = 2 := by
  Let's first prove that 1 = 1
  exact rfl
  Let's now prove that 2 = 2
  exact rfl
