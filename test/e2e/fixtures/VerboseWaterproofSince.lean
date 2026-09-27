-- An `Exercise` split over several code blocks, with only the proof body in the input area. The
-- exercise is still checked as a whole, and only its steps in the input area are probed.
--
-- Same exercise as VerboseSinceWeConclude.lean.
--
-- Findings with the fixture probes (`decide`, `tauto`, `omega`, `norm_num`, `simp`, `ring`) are in
-- expected/VerboseWaterproofSince.test.json; raw-tactic errors in expected/errors.txt.
import Goudlokje
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
