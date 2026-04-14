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

```lean
Exercise "1.1.13_extra"
  Given: (p q r : Prop)
  Assume: (_ : p)
  Conclusion: (p ∨ q) ∨ r
Proof:
  Let's prove that p ∨ q
  · Let's prove that p
    · We conclude by hypothesis
QED
```

```lean
Example "1.1.20"
  Given: (p q r : Prop)
  Assume: (_ : (p ∨ q) ∧ r)
  Conclusion: p ∨ (q ∧ r)
Proof:
  Since (p ∨ q) ∧ r we get that p ∨ q and r
  We discuss depending on whether p or q
  · Assume that p
    Let's prove that p
    · We conclude by hypothesis
  · Assume that q
    Let's prove that q ∧ r
    · Since q and r we conclude that q ∧ r
QED
```

```lean
Exercise "1.1.21"
  Given: (p q r : Prop)
  Assume: (_ : q ∨ r)
  Conclusion: (p ∨ q) ∨ (p ∨ r)
Proof:
  We discuss depending on whether q or r
  · Assume that q
    Let's prove that p ∨ q
    · Let's prove that q
      · We conclude by hypothesis
  · Assume that r
    Let's prove that p ∨ r
    · Let's prove that r
      · We conclude by hypothesis
QED
```

```lean
Example "1.2.25"
  Given:
  Assume:
  Conclusion: ∃ n : ℤ, (∃ k : ℤ, k * k = n) ∧ (∃ l : ℤ, l * l * l + 1 = n)
Proof:
  Let's prove that 9 works
  Let's first prove that ∃ k : ℤ, k * k = 9
  · Let's prove that 3 works
    We compute
  Let's now prove that ∃ l : ℤ, l * l * l + 1 = 9
  · Let's prove that 2 works
    We compute
QED
```
