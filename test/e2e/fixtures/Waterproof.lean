-- Proofs without Lean Verbose, in Waterproof code blocks without an input area: not checked. No
-- .test.json, no errors.
import Goudlokje
import WaterproofGenre
import Mathlib.Tactic.NormNum
open WaterproofGenre

#doc (WaterproofGenre) "Test Exercise" =>

```lean
-- Not checked (no Verbose, no input area).
example : 1 + 1 = 2 := by
  norm_num
```

```lean
-- Not checked (no Verbose, no input area).
example : 2 + 2 = 4 ∧ 3 + 3 = 6 := by
  constructor
  · norm_num
  · norm_num
```
