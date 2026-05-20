-- Fixture for CheckB1 (raw Lean tactic detection) tests.
-- Contains raw Lean tactics in proof bodies that CheckB1 should flag.
import Verbose.English.All

set_option linter.unusedTactic false

::::multilean
:::input
```lean
-- Fixture for CheckB1 (raw Lean tactic detection) tests.
-- Contains raw Lean tactics in proof bodies that CheckB1 should flag.

set_option linter.unusedTactic false

-- Example using raw Lean tactics (`constructor`, `trivial`) instead of
-- Verbose commands.  CheckB1 should flag each raw tactic position.
example : True ∧ True := by
  constructor
  · trivial
  · trivial
```
:::
::::
