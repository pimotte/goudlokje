-- typeAscription (B2): type annotations in Verbose proofs are warnings, recorded as expected in
-- .test.json by `update`.
--
-- Findings with the fixture probes (`decide`, `tauto`, `omega`, `norm_num`, `simp`, `ring`) are in
-- expected/LintB2.test.json; raw-tactic errors in expected/errors.txt.
import Goudlokje
import Verbose.English.All
import WaterproofGenre
open WaterproofGenre

set_option linter.unusedTactic false

#doc (WaterproofGenre) "typeAscription (B2)" =>

::::multilean
:::input
```lean
set_option linter.unusedTactic false

-- `Fix n : ℕ` is a type annotation (step 2).
example : (∀ n : ℕ, n + 0 = n) ∧ True := by
  Let's first prove that ∀ n : ℕ, n + 0 = n
  Fix n : ℕ
  ring
  Let's now prove that True
  trivial

-- `(trivial : True)` is a type annotation (step 2).
example : True ∧ True := by
  Let's first prove that True
  exact (trivial : True)
  Let's now prove that True
  trivial
```
:::
::::
