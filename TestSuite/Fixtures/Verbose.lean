-- Fixture file for Goudlokje Verbose Lean integration tests.
-- Uses Verbose English tactics where `decide` can shortcut intermediate steps.
import Verbose.English.All

set_option linter.unusedTactic false

-- A two-part conjunction proved with Verbose tactics.
-- After "Let's first prove that 1 + 1 = 2", the goal is `1 + 1 = 2`, which
-- `decide` can close directly (shortcut at the `norm_num` step).
example : 1 + 1 = 2 ∧ 2 + 2 = 4 := by
  Let's first prove that 1 + 1 = 2
  norm_num
  Let's now prove that 2 + 2 = 4
  norm_num

-- A simple existential proof using Verbose witness tactic.
-- Goal at `rfl` is `4 = 2 * 2`; `decide` can close it.
example : ∃ k : ℕ, 4 = 2 * k := by
  Let's prove that 2 works
  rfl
