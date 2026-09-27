-- Proofs without Lean Verbose are not checked at all: this `sorry` (B3) and this type annotation
-- (B2) are not reported. No .test.json, no errors.
import Goudlokje
import WaterproofGenre
open WaterproofGenre

#doc (WaterproofGenre) "Non-Verbose lint fixture" =>

::::multilean
:::input
```lean
set_option warn.sorry false

-- Not a Verbose proof: the `sorry` is not reported.
example : True := by
  sorry

-- Not a Verbose proof: `(trivial : True)` is not reported.
example : True ∧ True := by
  exact And.intro (trivial : True) trivial
```
:::
::::
