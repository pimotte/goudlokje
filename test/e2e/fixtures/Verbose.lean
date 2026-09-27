-- Verbose proofs inside a Waterproof input area.
--
-- Findings with the fixture probes (`decide`, `tauto`, `omega`, `norm_num`, `simp`, `ring`) are in
-- expected/Verbose.test.json; raw-tactic errors in expected/errors.txt.
import Goudlokje
import Verbose.English.All
import WaterproofGenre
open WaterproofGenre

set_option linter.unusedTactic false

#doc (WaterproofGenre) "Verbose Lean integration fixture" =>

::::multilean
:::input
```lean
set_option linter.unusedTactic false

-- Shortcuts at step 1 (the whole conjunction) and, for `tauto`, at step 3. The `norm_num`
-- steps close their goals, so they are not probed.
example : 1 + 1 = 2 ∧ 2 + 2 = 4 := by
  Let's first prove that 1 + 1 = 2
  norm_num
  Let's now prove that 2 + 2 = 4
  norm_num

-- No shortcut: `Let's prove that 2 works` leaves `4 = 2 * 2`, which `rfl` closes as the
-- last step, and no probe proves the existential at step 1.
example : ∃ k : ℕ, 4 = 2 * k := by
  Let's prove that 2 works
  rfl
```
:::
::::
