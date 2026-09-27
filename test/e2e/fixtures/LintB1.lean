-- rawTactic (B1) is only checked in Verbose proofs.
--
-- The proof below uses only raw Lean tactics (`constructor`, `trivial`) and no Lean Verbose, so
-- nothing is reported: no .test.json, no errors.
import Goudlokje
import Verbose.English.All
import WaterproofGenre
open WaterproofGenre

set_option linter.unusedTactic false

#doc (WaterproofGenre) "rawTactic (B1): proofs without Verbose" =>

::::multilean
:::input
```lean
set_option linter.unusedTactic false

-- Not a Verbose proof: not checked.
example : True ∧ True := by
  constructor
  · trivial
  · trivial
```
:::
::::
