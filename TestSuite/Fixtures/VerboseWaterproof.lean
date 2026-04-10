-- Fixture for Goudlokje integration tests: Lean Verbose proofs inside WaterproofGenre #doc blocks.
-- This combines both packages: WaterproofGenre for document structure, Verbose.English.All for proofs.
-- After each Verbose step boundary, the sub-goal should be closeable by `decide`.
import WaterproofGenre
open WaterproofGenre

#doc (WaterproofGenre) "Test Exercise with Verbose Proofs" =>

```lean
set_option linter.unusedTactic false
-- Goal at `norm_num` (inside first Verbose step) is `1 + 1 = 2`; `decide` can close it.
example : 1 + 1 = 2 ∧ 2 + 2 = 4 := by
  Let's first prove that 1 + 1 = 2
  norm_num
  Let's now prove that 2 + 2 = 4
  norm_num
```
