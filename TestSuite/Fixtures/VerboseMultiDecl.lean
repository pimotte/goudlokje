-- Fixture for testing that step filtering resets per declaration.
-- Declaration 1 uses Verbose step boundaries; Declaration 2 does not.
import Verbose.English.All
import WaterproofGenre
open Verbose English
open WaterproofGenre

set_option linter.unusedTactic false

#doc (WaterproofGenre) "Multi-declaration filter fixture" =>

::::multilean
:::input
```lean
-- Fixture for testing that step filtering resets per declaration.
-- Declaration 1 uses Verbose step boundaries; Declaration 2 does not.

set_option linter.unusedTactic false

-- Decl 1: two Verbose steps, each with a noop `show` before `norm_num`.
-- The filter keeps only `show` per step; skip-last removes step 2 → 1 decide shortcut.
example : 1 + 1 = 2 ∧ 2 + 2 = 4 := by
  Let's first prove that 1 + 1 = 2
  show 1 + 1 = 2
  norm_num
  Let's now prove that 2 + 2 = 4
  show 2 + 2 = 4
  norm_num

-- Decl 2: Verbose Exercise without step boundaries; filter must not suppress it.
-- Has two tactic positions: `show` (not last → shortcut), `norm_num` (last → skipped).
Exercise "multi-decl test without step boundaries"
  Given: (dummy : Nat)
  Conclusion: 1 + 1 = 2
Proof:
  show 1 + 1 = 2   -- noop; `decide` can close the goal here (not the last step → shortcut)
  norm_num          -- closes the goal; last → skip
QED
```
:::
::::
