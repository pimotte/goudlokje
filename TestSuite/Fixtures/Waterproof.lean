-- Fixture file for Goudlokje Waterproof Genre integration tests.
-- Uses the Waterproof Genre `#doc` format; Lean code blocks inside have
-- standard proofs where `decide` can shortcut intermediate steps.
import WaterproofGenre
open Verso.Genre.Manual.InlineLean

#doc (Verso.Genre.Manual) "Test Exercise" =>

```lean
-- Goal at `norm_num` is `1 + 1 = 2`; `decide` can close it directly.
example : 1 + 1 = 2 := by
  norm_num
```

```lean
-- Goal at each `norm_num` step can be closed by `decide`.
example : 2 + 2 = 4 ∧ 3 + 3 = 6 := by
  constructor
  · norm_num
  · norm_num
```
