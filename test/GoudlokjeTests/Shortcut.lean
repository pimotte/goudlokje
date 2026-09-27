import Goudlokje.Linter
import Verbose.English.All

/-! Tests for the shortcut linter. Expected shortcuts are listed in `Shortcut.test.json`. -/

set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option goudlokje.probes "decide"
-- This file tests shortcuts only.
set_option linter.goudlokje.rawTactic false

/-- A tactic that never terminates on its own, to test the probe budget. -/
elab "burn" : tactic => do
  repeat
    let _ ← Lean.Meta.mkFreshExprMVar (some (Lean.mkConst ``Nat))
    Lean.Core.checkSystem "burn"

-- Outside input areas nothing is probed.
#guard_msgs in
example : 1 + 1 = 2 ∧ 2 + 2 = 4 := by
  Let's first prove that 1 + 1 = 2
  show 1 + 1 = 2
  norm_num
  Let's now prove that 2 + 2 = 4
  norm_num

/-
:::input
-/

-- Per goal chain, only the first shortcut is reported. Verbose blocks the pending goal until
-- `Let's now prove that` (step 4), so in the second chain the first shortcut is at step 5.
/--
error: `decide` closes the goal at step 1 of exercise "example : 1 + 1 = 2 ∧ 2 + 2 = 4", so the rest of this part of the proof can be skipped

If this is intended, record it with `goudlokje update`.

Note: This linter can be disabled with `set_option linter.goudlokje.shortcut false`
---
error: `decide` closes the goal at step 2 of exercise "example : 1 + 1 = 2 ∧ 2 + 2 = 4", so the rest of this part of the proof can be skipped

If this is intended, record it with `goudlokje update`.

Note: This linter can be disabled with `set_option linter.goudlokje.shortcut false`
---
error: `decide` closes the goal at step 5 of exercise "example : 1 + 1 = 2 ∧ 2 + 2 = 4", so the rest of this part of the proof can be skipped

If this is intended, record it with `goudlokje update`.

Note: This linter can be disabled with `set_option linter.goudlokje.shortcut false`
-/
#guard_msgs in
example : 1 + 1 = 2 ∧ 2 + 2 = 4 := by
  Let's first prove that 1 + 1 = 2
  show 1 + 1 = 2
  norm_num
  Let's now prove that 2 + 2 = 4
  show 2 + 2 = 4
  norm_num

-- Proofs without Verbose tactics are not checked.
#guard_msgs in
example : 1 + 1 = 2 := by
  show 1 + 1 = 2
  norm_num

-- Every probe that succeeds at the first shortcut of a chain is reported; a probe that runs out
-- of heartbeats is not a shortcut.
set_option goudlokje.probes "burn;; decide;; norm_num" in
/--
error: `decide` closes the goal at step 1 of exercise "multiple probes", so the rest of this part of the proof can be skipped

If this is intended, record it with `goudlokje update`.

Note: This linter can be disabled with `set_option linter.goudlokje.shortcut false`
---
error: `norm_num` closes the goal at step 1 of exercise "multiple probes", so the rest of this part of the proof can be skipped

If this is intended, record it with `goudlokje update`.

Note: This linter can be disabled with `set_option linter.goudlokje.shortcut false`
-/
#guard_msgs in
Exercise "multiple probes"
  Given: (n : ℕ)
  Assume: (h : n = n)
  Conclusion: 1 + 1 = 2
Proof:
  show 1 + 1 = 2
  norm_num
QED

-- Expected shortcuts are not reported; expected shortcuts that no longer occur are stale.
/--
warning: expected shortcut `decide` at step 7 of exercise "with expectations" no longer occurs; remove it with `goudlokje update`

Note: This linter can be disabled with `set_option linter.goudlokje.shortcut false`
-/
#guard_msgs in
Exercise "with expectations"
  Given: (n : ℕ)
  Assume: (h : n = n)
  Conclusion: 1 + 1 = 2
Proof:
  show 1 + 1 = 2
  norm_num
QED

-- Unparsable probes are reported.
set_option goudlokje.probes "decide;; (" in
/--
error: cannot parse probe tactic `(`: <input>:1:1: unexpected end of input; expected '{'
-/
#guard_msgs in
example : 1 + 1 = 2 := by
  Let's prove that 1 + 1 = 2
  norm_num

/-
:::
-/
