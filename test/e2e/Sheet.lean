import Goudlokje
import Verbose.English.All
import WaterproofGenre
open Verbose English
open WaterproofGenre

#doc (WaterproofGenre) "End-to-end test worksheet" =>

Exercises for the end-to-end test of `goudlokje check` and `goudlokje update`.

::::multilean
:::input
```lean
Exercise "shortcut"
  Given: (n : ℕ)
  Assume: (h : n = n)
  Conclusion: 1 + 1 = 2
Proof:
  show 1 + 1 = 2
  norm_num
QED
```
:::
::::

::::multilean
:::input
```lean
Exercise "annotation"
  Given:
  Assume:
  Conclusion: ∀ n : ℕ, n + 0 = n
Proof:
  Fix n : ℕ
  norm_num
QED
```
:::
::::

::::multilean
:::input
```lean
Exercise "true or false"
  Given:
  Assume:
  Conclusion: 1 = 2
Proof:
  sorry
QED
```
:::
::::
