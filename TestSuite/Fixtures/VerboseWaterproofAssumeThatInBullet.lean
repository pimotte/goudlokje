-- Regression test fixture: `Assume for contradiction` inside a focused proof bullet.
-- Minimal reproduction of the bug in sheet1_subset.lean exercise 2.1.10.
-- Verifies that focused bullets containing Verbose step boundaries
-- (`Assume for contradiction`) do not produce false-positive shortcuts
-- when `filterVerboseSteps = true`.
import WaterproofGenre
import Verbose.English.All
open Verbose English
open WaterproofGenre

set_option linter.unusedTactic false

#doc (WaterproofGenre) "Assume for contradiction in focused bullet" =>

::::multilean
:::input
```lean
set_option linter.unusedTactic false

Example "2.1.10"
  Given: (p q : Prop)
  Assume: (_ : p) (_ : q)
  Conclusion: p ∧ q
Proof:
  Let's first prove that p
  · We conclude by hypothesis
  Let's now prove that q
  · Assume for contradiction that ¬ q
    We conclude by hypothesis
```
:::
::::
