-- sorry (B3): `sorry` in an exercise is an error, unless the exercise allows it.
--
-- The `sorry` steps close their goals, so they are never probed. Lean's own "declaration uses
-- `sorry`" warning is turned off (`warn.sorry false`); B3 does not depend on it. `update --all`
-- records `allowSorry` for the exercise.
--
-- Findings with the fixture probes (`decide`, `tauto`, `omega`, `norm_num`, `simp`, `ring`) are in
-- expected/LintB3.test.json; raw-tactic errors in expected/errors.txt.
import Goudlokje
import Verbose.English.All
import WaterproofGenre
open WaterproofGenre

set_option linter.unusedTactic false
set_option warn.sorry false

#doc (WaterproofGenre) "sorry (B3)" =>

::::multilean
:::input
```lean
set_option linter.unusedTactic false
set_option warn.sorry false

-- Both `sorry` steps are found; the exercise gets `allowSorry`.
example : True ∧ True := by
  Let's first prove that True
  sorry
  Let's now prove that True
  sorry
```
:::
::::
