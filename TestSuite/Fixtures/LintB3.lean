-- Fixture for CheckB3 (sorry detection) tests.
-- Contains `sorry` in a Verbose proof body that CheckB3 should flag.
import Verbose.English.All
import WaterproofGenre
open WaterproofGenre

set_option linter.unusedTactic false
set_option warn.sorry false

#doc (WaterproofGenre) "CheckB3 sorry fixture" =>

::::multilean
:::input
```lean
-- Fixture for CheckB3 (sorry detection) tests.
-- Contains `sorry` in a Verbose proof body that CheckB3 should flag.

set_option linter.unusedTactic false
set_option warn.sorry false

-- A Verbose proof with `sorry`: CheckB3 should detect and report the sorry.
example : True ∧ True := by
  Let's first prove that True
  sorry
  Let's now prove that True
  sorry
```
:::
::::
