-- Fixture for testing Lean Verbose step filtering.
-- Each step has two tactics: `show` (a no-op) followed by `norm_num`.
-- `decide` is a shortcut at BOTH positions within each step body.
-- The filter keeps only the first tactic per step (1 per step, at `show`).
-- Declaration-level skip-last then drops the last step's representative → 1 shortcut.
import Verbose.English.All
import WaterproofGenre
open WaterproofGenre

set_option linter.unusedTactic false

#doc (WaterproofGenre) "Verbose step filtering fixture" =>

::::multilean
:::input
```lean
-- Fixture for testing Lean Verbose step filtering.
-- Each step has two tactics: `show` (a no-op) followed by `norm_num`.
-- `decide` is a shortcut at BOTH positions within each step body.
-- The filter keeps only the first tactic per step (1 per step, at `show`).
-- Declaration-level skip-last then drops the last step's representative → 1 shortcut.

set_option linter.unusedTactic false

example : 1 + 1 = 2 ∧ 2 + 2 = 4 := by
  Let's first prove that 1 + 1 = 2
  show 1 + 1 = 2   -- noop; goal still 1+1=2 → decide shortcut (kept by filter)
  norm_num          -- closes the goal; goal is 1+1=2 → decide shortcut (suppressed by filter)
  Let's now prove that 2 + 2 = 4
  show 2 + 2 = 4   -- noop; goal still 2+2=4 → decide shortcut (kept by filter)
  norm_num          -- closes the goal; goal is 2+2=4 → decide shortcut (suppressed by filter)
```
:::
::::
