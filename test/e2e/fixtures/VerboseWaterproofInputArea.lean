-- Only student input areas (between `:::input` and `:::`) are checked. The two exercises are the
-- same; only the one inside the input area is reported: step 1 (`show`) is a shortcut for every
-- probe, and `show` and `norm_num` are raw tactics.
--
-- Findings with the fixture probes (`decide`, `tauto`, `omega`, `norm_num`, `simp`, `ring`) are in
-- expected/VerboseWaterproofInputArea.test.json; raw-tactic errors in expected/errors.txt.
import Goudlokje
import Verbose.English.All
import WaterproofGenre
open Verbose English
open WaterproofGenre

set_option linter.unusedTactic false

#doc (WaterproofGenre) "Input area scoping fixture" =>

::::multilean
:::input
```lean
-- Inside the input area: checked.

set_option linter.unusedTactic false

Exercise "inside-area"
  Given: (dummy : Nat)
  Assume: (h : 0 = 0)
  Conclusion: 1 + 1 = 2
Proof:
  show 1 + 1 = 2   -- leaves a goal: probed, a shortcut
  norm_num          -- closes the goal: not probed
QED
```
:::
::::

```lean
-- Outside any input area: not checked.
Exercise "outside-area"
  Given: (dummy : Nat)
  Assume: (h : 0 = 0)
  Conclusion: 1 + 1 = 2
Proof:
  show 1 + 1 = 2
  norm_num
QED
```
