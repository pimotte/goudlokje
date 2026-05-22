-- Fixture file for Goudlokje integration tests.
-- This file contains proofs that are intentionally shortcuttable by `decide`.
import WaterproofGenre
open WaterproofGenre

#doc (WaterproofGenre) "Simple non-Verbose fixture" =>

::::multilean
:::input
```lean
-- Fixture file for Goudlokje integration tests.
-- This file contains proofs that are intentionally shortcuttable by `decide`.
-- It imports nothing beyond the core Lean 4 prelude.

/-- A trivially decidable proposition. `decide` can close this goal immediately. -/
theorem onePlusOneEqTwo : 1 + 1 = 2 := by
  rfl

/-- A two-step proof where `decide` can shortcut both sub-goals. -/
theorem twoStepAnd : True ∧ True := by
  constructor
  · trivial
  · trivial
```
:::
::::
