import WaterproofGenre
import Verbose.English.All
open WaterproofGenre

#doc (WaterproofGenre) "Test Since Exercise" =>

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
