-- Proofs without Lean Verbose are not checked, even in an input area: `decide` could shortcut these
-- proofs, but nothing is reported. No .test.json, no errors.
import Goudlokje
import WaterproofGenre
open WaterproofGenre

#doc (WaterproofGenre) "Simple non-Verbose fixture" =>

::::multilean
:::input
```lean
-- It imports nothing beyond the core Lean 4 prelude.

/-- A one-step proof: never a shortcut, and not a Verbose proof anyway. -/
theorem onePlusOneEqTwo : 1 + 1 = 2 := by
  rfl

/-- `decide` could close the goal at `constructor`, but this is not a Verbose proof. -/
theorem twoStepAnd : True ∧ True := by
  constructor
  · trivial
  · trivial
```
:::
::::
