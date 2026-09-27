-- rawTactic (B1): raw Lean tactics in a Verbose proof are errors.
--
-- The Verbose steps (`Let's first/now prove that`) make this a Verbose proof, so both `exact` steps
-- are reported.
--
-- Findings with the fixture probes (`decide`, `tauto`, `omega`, `norm_num`, `simp`, `ring`) are in
-- expected/LintB1VerboseCheck.test.json; raw-tactic errors in expected/errors.txt.
import Goudlokje
import Verbose.English.All
import WaterproofGenre
open WaterproofGenre

set_option linter.unusedTactic false

#doc (WaterproofGenre) "rawTactic (B1): raw tactics in a Verbose proof" =>

::::multilean
:::input
```lean
set_option linter.unusedTactic false

-- `exact` is reported at steps 2 and 4.
example : 1 = 1 ∧ 2 = 2 := by
  Let's first prove that 1 = 1
  exact rfl
  Let's now prove that 2 = 2
  exact rfl
```
:::
::::
