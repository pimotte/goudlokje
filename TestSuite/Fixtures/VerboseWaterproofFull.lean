import WaterproofGenre
import Verbose.English.All
open WaterproofGenre

#doc (WaterproofGenre) "Test Exercise with Full Verbose Proofs" =>



::::multilean
```lean
Exercise "1.1.13"
  Given: (p q r : Prop)
  Assume: (_ : p) (_ : q) (_ : r)
  Conclusion: p ∧ q ∧ r
Proof:
```
:::input
```lean
  Since p and q we get that p ∧ q
  Since p ∧ q and r we conclude that p ∧ q ∧ r
```
:::
```lean
QED
```
::::


```lean
Exercise "1.1.14"
  Given: (p q r : Prop)
  Assume: (_ : p) (_ : q)
  Conclusion: p ∧ q
Proof:
  Let's first prove that p
  · We conclude by hypothesis
  Let's now prove that q
  · We conclude by hypothesis
QED
```
