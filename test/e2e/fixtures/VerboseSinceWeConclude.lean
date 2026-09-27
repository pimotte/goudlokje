-- `Since … we get that` and `Since … we conclude that` elaborate to several internal tactics at the
-- same position. Only the tactics as written are steps: step 1 (`Since … we get that`) leaves a goal
-- and is probed (only `tauto` closes it); step 2 closes the goal.
--
-- Same exercise as VerboseWaterproofSince.lean.
--
-- Findings with the fixture probes (`decide`, `tauto`, `omega`, `norm_num`, `simp`, `ring`) are in
-- expected/VerboseSinceWeConclude.test.json; raw-tactic errors in expected/errors.txt.
import Goudlokje
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
