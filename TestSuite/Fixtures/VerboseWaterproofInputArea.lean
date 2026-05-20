-- Fixture for testing input area scoping in Waterproof files.
-- Shortcut inside the :::input block is detected; shortcut outside is not.
import WaterproofGenre
import Verbose.English.All
open WaterproofGenre

::::multilean
```lean
-- Fixture for testing input area scoping in Waterproof files.
-- Shortcut inside the :::input block is detected; shortcut outside is not.

set_option linter.unusedTactic false

-- This proof is OUTSIDE the input area: shortcuts should NOT be detected.
example : True ∧ True := by
  Let's first prove that True
  decide
  Let's now prove that True
  decide
```
:::input
-- This proof is INSIDE the input area: shortcuts SHOULD be detected.
Exercise "inside-area"
  Given: ()
  Conclusion: True ∧ True
Proof:
  Let's first prove that True
  decide
  Let's now prove that True
  decide
QED
:::
::::
