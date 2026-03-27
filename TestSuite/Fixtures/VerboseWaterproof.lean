-- Fixture for Goudlokje integration tests: Lean Verbose proofs inside WaterproofGenre #doc blocks.
-- This combines both packages: WaterproofGenre for document structure, Verbose.English.All for proofs.
-- After each Verbose step boundary, the sub-goal should be closeable by `decide`.
import WaterproofGenre
import Verbose.English.All
open Verso.Genre.Manual.InlineLean

#doc (Verso.Genre.Manual) "Test Exercise with Verbose Proofs" =>

```lean
set_option linter.unusedTactic false
-- Goal before `rfl` (inside first Verbose step) is `1 + 1 = 2`; `decide` can close it.
example : 1 + 1 = 2 ∧ 2 + 2 = 4 := by
  Let's first prove that 1 + 1 = 2
  rfl
  Let's now prove that 2 + 2 = 4
  rfl
```
