-- A Verbose proof in a Waterproof code block without an input area (`:::input`): nothing outside
-- input areas is checked, so nothing is reported. No .test.json, no errors.
import Goudlokje
import WaterproofGenre
import Verbose.English.All
open WaterproofGenre

#doc (WaterproofGenre) "Test Exercise with Verbose Proofs" =>

```lean
set_option linter.unusedTactic false
-- Not in an input area: not checked.
example : 1 + 1 = 2 ∧ 2 + 2 = 4 := by
  Let's first prove that 1 + 1 = 2
  norm_num
  Let's now prove that 2 + 2 = 4
  norm_num
```
