-- Goal chains: steps working on the same goal form a chain, and only the first shortcut in a chain
-- is reported.
--
-- Step 1 (`Let's first prove that`) works on the whole conjunction: its own chain. Step 2 (`show`)
-- works on the first part: a new chain, reported. Steps 4 and 5 both work on the second part: at
-- step 4 Verbose still blocks the goal, so only `tauto` closes it there and step 5 (which every
-- probe would close) is not reported separately. The `norm_num` steps close their goals and are not
-- probed.
--
-- Findings with the fixture probes (`decide`, `tauto`, `omega`, `norm_num`, `simp`, `ring`) are in
-- expected/VerboseMultiStep.test.json; raw-tactic errors in expected/errors.txt.
import Goudlokje
import Verbose.English.All
import WaterproofGenre
open WaterproofGenre

set_option linter.unusedTactic false

#doc (WaterproofGenre) "Goal chains" =>

::::multilean
:::input
```lean
set_option linter.unusedTactic false

example : 1 + 1 = 2 ∧ 2 + 2 = 4 := by
  Let's first prove that 1 + 1 = 2
  show 1 + 1 = 2   -- step 2: first shortcut of its chain
  norm_num          -- closes its goal: not probed
  Let's now prove that 2 + 2 = 4
  show 2 + 2 = 4   -- step 5: same chain as step 4, not reported
  norm_num          -- closes its goal: not probed
```
:::
::::
