-- Fixture for testing input area scoping.
-- Shortcuts inside :::input are detected; shortcuts outside are not.
import Verbose.English.All
import WaterproofGenre
open Verbose English
open WaterproofGenre

set_option linter.unusedTactic false

#doc (WaterproofGenre) "Input area scoping fixture" =>

::::multilean
:::input
```lean
-- This proof is INSIDE the input area: shortcuts SHOULD be detected.

set_option linter.unusedTactic false

Exercise "inside-area"
  Given: (dummy : Nat)
  Assume: (h : 0 = 0)
  Conclusion: 1 + 1 = 2
Proof:
  show 1 + 1 = 2   -- noop; `decide` closes goal here (not last → shortcut)
  norm_num          -- closes the goal; last → skip
QED
```
:::
::::
