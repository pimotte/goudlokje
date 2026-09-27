-- rawTactic (B1) judges tactics as the student wrote them.
--
-- Verbose tactics (`Let's first prove that`, `Let's prove that 2 works`) expand to raw Lean tactics
-- internally, but are never reported. The raw tactics written here (`norm_num`, `rfl`) are, since
-- the fixtures allow no raw tactics (`goudlokje.allowedTactics`).
--
-- Findings with the fixture probes (`decide`, `tauto`, `omega`, `norm_num`, `simp`, `ring`) are in
-- expected/LintB1Verbose.test.json; raw-tactic errors in expected/errors.txt.
import Goudlokje
import Verbose.English.All
import WaterproofGenre
open WaterproofGenre

set_option linter.unusedTactic false

#doc (WaterproofGenre) "rawTactic (B1): Verbose tactics" =>

::::multilean
:::input
```lean
set_option linter.unusedTactic false

-- `Let's first/now prove that`: Verbose, not reported. `norm_num`: reported (steps 2, 4).
example : 1 + 1 = 2 ∧ 2 + 2 = 4 := by
  Let's first prove that 1 + 1 = 2
  norm_num
  Let's now prove that 2 + 2 = 4
  norm_num

-- `Let's prove that 2 works`: Verbose, not reported. `rfl`: reported (step 2).
example : ∃ k : ℕ, 4 = 2 * k := by
  Let's prove that 2 works
  rfl
```
:::
::::
