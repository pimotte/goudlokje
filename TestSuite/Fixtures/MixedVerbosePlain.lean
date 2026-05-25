-- Fixture: Mixed Verbose and non-Verbose proofs in the same file.
-- Verbose proofs should produce shortcuts; non-Verbose proofs should not.
import Verbose.English.All
import WaterproofGenre
open WaterproofGenre

#doc (WaterproofGenre) "Mixed Verbose and non-Verbose fixture" =>

::::multilean
:::input
```lean
import Verbose.English.All
import WaterproofGenre
open WaterproofGenre

theorem verboseEx : 1 + 1 = 2 ∧ 2 + 2 = 4 := by
  Let's first prove that 1 + 1 = 2
    show 1 + 1 = 2
    decide

theorem plainEx : 3 + 3 = 6 := by
  decide
```
:::
::::
