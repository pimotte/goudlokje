-- Fixture: Non-Verbose proof (no Verbose step boundaries).
-- This file is used to verify that non-Verbose proofs produce no shortcut entries.
import WaterproofGenre
open WaterproofGenre

#doc (WaterproofGenre) "Plain proof fixture" =>

::::multilean
:::input
```lean
-- Plain non-Verbose proof with no Let's prove that / Let's first prove that boundaries.
example : 1 + 1 = 2 := by
  rfl

theorem twoAnd : True ∧ True := by
  constructor
  · trivial
  · trivial
```
:::
::::
