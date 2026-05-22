-- Fixture for testing Lean Verbose step filtering with multi-tactic steps.
-- Each step has two `norm_num` tactics. `norm_num` has kind `Mathlib.Tactic.normNum`
-- which is NOT in `rawLeanTacticKinds` (which uses `Lean.Parser.Tactic.normNum`),
-- so it does NOT trigger B1 violations.
import Verbose.English.All
import WaterproofGenre
open WaterproofGenre

set_option linter.unusedTactic false

#doc (WaterproofGenre) "Verbose step filtering fixture (multi-norm_num)" =>

::::multilean
:::input
```lean
-- Fixture for testing Lean Verbose step filtering with multi-tactic steps.
-- Each step has two `norm_num` tactics.
-- `decide` is a shortcut at the first `norm_num` position (kept by filter).
-- The second `norm_num` is suppressed by per-step skip-last.

set_option linter.unusedTactic false

example : 1 + 1 = 2 ∧ 2 + 2 = 4 := by
  Let's first prove that 1 + 1 = 2
  norm_num
  norm_num
  Let's now prove that 2 + 2 = 4
  norm_num
  norm_num
```
:::
::::
