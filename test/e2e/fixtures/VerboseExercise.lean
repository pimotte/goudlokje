-- A Verbose `Exercise` expands to `example … := by with(out)_suggestions <proof>; done`, where the
-- wrapper tactic sits at the `Proof:` token and has the whole conclusion as its goal. Steps are
-- taken from the proof as written, so the wrapper is never a step and never probed.
--
-- Step 1 (`show`) leaves a goal and is probed: every probe closes it. Step 2 (`norm_num`) closes its
-- goal and is not probed.
--
-- Findings with the fixture probes (`decide`, `tauto`, `omega`, `norm_num`, `simp`, `ring`) are in
-- expected/VerboseExercise.test.json; raw-tactic errors in expected/errors.txt.
import Goudlokje
import Verbose.English.All
import WaterproofGenre
open Verbose English
open WaterproofGenre

set_option linter.unusedTactic false

#doc (WaterproofGenre) "Verbose Exercise wrapper fixture" =>

::::multilean
:::input
```lean
set_option linter.unusedTactic false

Exercise "test exercise without step boundaries"
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
