-- Fixture for testing Lean Verbose step filtering.
-- Each step has two tactics: `show` (a no-op) followed by `norm_num`.
-- `decide` is a shortcut at BOTH positions within each step body.
-- With filterVerboseSteps = false: 4 shortcuts total (2 per step, at `show` and `norm_num`).
-- With filterVerboseSteps = true:  2 shortcuts total (1 per step, only at `show`).
import Verbose.English.All

set_option linter.unusedTactic false

example : 1 + 1 = 2 ∧ 2 + 2 = 4 := by
  Let's first prove that 1 + 1 = 2
  show 1 + 1 = 2   -- noop; goal still 1+1=2 → decide shortcut (kept by filter)
  norm_num          -- closes the goal; goal is 1+1=2 → decide shortcut (suppressed by filter)
  Let's now prove that 2 + 2 = 4
  show 2 + 2 = 4   -- noop; goal still 2+2=4 → decide shortcut (kept by filter)
  norm_num          -- closes the goal; goal is 2+2=4 → decide shortcut (suppressed by filter)
