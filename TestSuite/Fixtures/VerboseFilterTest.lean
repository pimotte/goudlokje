-- Fixture for testing filter behavior with multi-tactic steps.
-- Each step has `show` (no-op, triggers B1) followed by `norm_num` (Mathlib tactic).
-- But `norm_num` is a Mathlib tactic (kind `Mathlib.Tactic.normNum`) which is NOT
-- in `rawLeanTacticKinds` (which uses `Lean.Parser.Tactic.normNum`), so it doesn't
-- trigger B1. The `show` does trigger B1, but we suppress it in the test by using
-- a `.test.json` file.
--
-- Actually, this fixture has NO `.test.json`, so B1 violations from `show` would count.
-- The correct approach is to use a fixture with NO raw Lean tactics that trigger B1.
--
-- Since `norm_num` inside a Verbose step is not collected as a TacticInfo when it's
-- the only tactic, we use `show` + `norm_num` for the multi-tactic step.
-- But `show` triggers B1. So we need a `.test.json` to suppress B1 violations.
--
-- For now, this fixture is used in tests where B1 violations are expected and counted.
import Verbose.English.All
import WaterproofGenre
open WaterproofGenre

set_option linter.unusedTactic false

#doc (WaterproofGenre) "Verbose filter test fixture" =>

::::multilean
:::input
```lean
example : 1 + 1 = 2 ∧ 2 + 2 = 4 := by
  Let's first prove that 1 + 1 = 2
  show 1 + 1 = 2
  norm_num
  Let's now prove that 2 + 2 = 4
  show 2 + 2 = 4
  norm_num
```
:::
::::
