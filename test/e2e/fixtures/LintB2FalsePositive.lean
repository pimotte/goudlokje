-- typeAscription (B2) must not report anything here: there are no type annotations in the proof
-- steps, only binders in statements and Verbose tactics that elaborate to type ascriptions
-- internally. B2 only looks at the syntax of the steps, so none of these count.
--
-- Findings with the fixture probes (`decide`, `tauto`, `omega`, `norm_num`, `simp`, `ring`) are in
-- expected/LintB2FalsePositive.test.json; raw-tactic errors in expected/errors.txt. Neither contains
-- a typeAscription entry.
import Goudlokje
import Verbose.English.All
import WaterproofGenre
open WaterproofGenre

set_option linter.unusedTactic false

#doc (WaterproofGenre) "typeAscription (B2): no false positives" =>

::::multilean
:::input
```lean
set_option linter.unusedTactic false

-- `∀ n : ℕ` is a binder in the statement, and `Fix n` has no type.
example : ∀ n : ℕ, n + 0 = n := by
  Fix n
  ring

-- `Let's prove that 2 works` elaborates to a type ascription internally.
example : ∃ k : ℕ, 4 = 2 * k := by
  Let's prove that 2 works
  rfl

-- `Let's first/now prove that` state goals, without type annotations.
example : 1 + 1 = 2 ∧ 2 + 2 = 4 := by
  Let's first prove that 1 + 1 = 2
  norm_num
  Let's now prove that 2 + 2 = 4
  norm_num
```
:::
::::
