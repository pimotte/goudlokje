-- Steps that close their own goal are never probed: a shortcut there saves no proof lines. In
-- particular the last step of a proof is never a shortcut.
--
-- Here both `norm_num` steps close their goal, so only the Verbose steps are probed: step 1 (`Let's
-- first prove that`, whose goal is the whole conjunction; every probe but `ring` closes it) and step
-- 3 (`Let's now prove that`, whose goal Verbose blocks until then; only `tauto` sees through that).
--
-- Findings with the fixture probes (`decide`, `tauto`, `omega`, `norm_num`, `simp`, `ring`) are in
-- expected/SkipLastStep.test.json; raw-tactic errors in expected/errors.txt.
import Goudlokje
import Verbose.English.All
import WaterproofGenre
open WaterproofGenre

set_option linter.unusedTactic false

#doc (WaterproofGenre) "Skip-last-step fixture" =>

::::multilean
:::input
```lean
set_option linter.unusedTactic false

example : 1 + 1 = 2 ∧ 2 + 2 = 4 := by
  Let's first prove that 1 + 1 = 2
  norm_num   -- closes its goal: not probed
  Let's now prove that 2 + 2 = 4
  norm_num   -- closes its goal (the last step): not probed
```
:::
::::
