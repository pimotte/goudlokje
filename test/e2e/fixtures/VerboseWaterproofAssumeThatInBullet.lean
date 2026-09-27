-- Verbose steps inside focusing bullets (`·`): the bullets are not steps, the tactics inside them
-- are.
--
-- Step 1 (`Let's first prove that p`) works on the whole conjunction and step 3 (`Let's now prove
-- that q`) on the blocked second part; `tauto` closes both. `Assume for contradiction that ¬ q`
-- (step 4) is in the same chain as step 3, so it is not reported separately.
--
-- Findings with the fixture probes (`decide`, `tauto`, `omega`, `norm_num`, `simp`, `ring`) are in
-- expected/VerboseWaterproofAssumeThatInBullet.test.json; raw-tactic errors in expected/errors.txt.
import Goudlokje
import WaterproofGenre
import Verbose.English.All
open Verbose English
open WaterproofGenre

set_option linter.unusedTactic false

#doc (WaterproofGenre) "Assume for contradiction in focused bullet" =>

::::multilean
:::input
```lean
set_option linter.unusedTactic false

Example "2.1.10"
  Given: (p q : Prop)
  Assume: (_ : p) (_ : q)
  Conclusion: p ∧ q
Proof:
  Let's first prove that p
  · We conclude by hypothesis
  Let's now prove that q
  · Assume for contradiction that ¬ q
    Since q and ¬ q we conclude that False
QED
```
:::
::::
