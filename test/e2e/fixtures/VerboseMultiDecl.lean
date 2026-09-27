-- Several exercises in one code block are checked independently, each with its own step numbers and
-- goal chains. The anonymous `example` is named after its statement.
--
-- Findings with the fixture probes (`decide`, `tauto`, `omega`, `norm_num`, `simp`, `ring`) are in
-- expected/VerboseMultiDecl.test.json; raw-tactic errors in expected/errors.txt.
import Goudlokje
import Verbose.English.All
import WaterproofGenre
open Verbose English
open WaterproofGenre

set_option linter.unusedTactic false

#doc (WaterproofGenre) "Several exercises in one block" =>

::::multilean
:::input
```lean
set_option linter.unusedTactic false

-- Chains: step 1 (whole conjunction); step 2 (`show`, first part); steps 4-5 (second part;
-- Verbose blocks its goal at step 4, so only `tauto` fires there and step 5 is not reported).
example : 1 + 1 = 2 ∧ 2 + 2 = 4 := by
  Let's first prove that 1 + 1 = 2
  show 1 + 1 = 2
  norm_num
  Let's now prove that 2 + 2 = 4
  show 2 + 2 = 4
  norm_num

-- Step 1 (`show`) is a shortcut; step 2 closes the goal and is not probed.
Exercise "multi-decl test without step boundaries"
  Given: (dummy : Nat)
  Assume:
  Conclusion: 1 + 1 = 2
Proof:
  show 1 + 1 = 2   -- leaves a goal: probed, a shortcut
  norm_num          -- closes the goal: not probed
QED
```
:::
::::
