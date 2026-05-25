-- Fixture: Multiple exercises in one file, each with its own Verbose proof.
-- Used to verify that step numbers are scoped per exercise (not per declaration).
import Verbose.English.All
import WaterproofGenre
open WaterproofGenre

#doc (WaterproofGenre) "Multi-exercise fixture" =>

::::multilean
:::input
```lean
import Verbose.English.All
import WaterproofGenre
open WaterproofGenre

theorem first : 1 + 1 = 2 ∧ 2 + 2 = 4 := by
  Let's first prove that 1 + 1 = 2
    show 1 + 1 = 2
    decide

theorem second : 3 + 3 = 6 := by
  Let's first prove that 3 + 3 = 6
    rw [Nat.add_comm 3 3]
    decide
```
:::
::::
