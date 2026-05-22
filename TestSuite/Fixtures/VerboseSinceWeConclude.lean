-- Regression test fixture for internal elaboration artifact bug (sheet1_subset.lean #2).
-- Verbose `Since...we get that` steps are NOT opaque and NOT step boundaries.
-- They elaborate into internal child nodes (Lean.Parser.Tactic.*) at the same position.
-- Without `isUserFacingVerboseTactic` filter, these children would be collected as
-- probe positions, potentially producing false-positive shortcuts.
import WaterproofGenre
import Verbose.English.All
open WaterproofGenre

#doc (WaterproofGenre) "Test Since elaboration artifact positions" =>

::::multilean
```lean
Exercise "1.1.13"
  Given: (p q r : Prop)
  Assume: (_ : (p ∧ q) ∧ r)
  Conclusion: q
Proof:
```
:::input
```lean
  Since (p ∧ q) ∧ r we get that p ∧ q
  Since p ∧ q we conclude that q
```
:::
```lean
QED
```
::::
