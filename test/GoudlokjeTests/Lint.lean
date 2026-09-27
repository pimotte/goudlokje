import Goudlokje.Linter
import Verbose.English.All
import GoudlokjeTests.CustomTactic

/-! Tests for the lint checks (B1–B3). Expectations are listed in `Lint.test.json`. -/

set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option warn.sorry false

/-
:::input
-/

/-! ## B1: raw Lean tactics -/

-- Raw Lean tactics in a Verbose proof are errors.
/--
error: raw Lean tactic `exact` at step 2 of exercise "example : True ∧ True"; use a Lean Verbose tactic instead

Tactics can be allowed for a whole project with the option `goudlokje.allowedTactics`.

Note: This linter can be disabled with `set_option linter.goudlokje.rawTactic false`
---
error: raw Lean tactic `constructor` at step 4 of exercise "example : True ∧ True"; use a Lean Verbose tactic instead

Tactics can be allowed for a whole project with the option `goudlokje.allowedTactics`.

Note: This linter can be disabled with `set_option linter.goudlokje.rawTactic false`
-/
#guard_msgs in
example : True ∧ True := by
  Let's first prove that True
  exact trivial
  Let's now prove that True
  constructor

-- Allowed tactics are not reported.
set_option goudlokje.allowedTactics "exact;; constructor" in
#guard_msgs in
example : True ∧ True := by
  Let's first prove that True
  exact trivial
  Let's now prove that True
  constructor

-- Tactics declared outside the Verbose modules are raw Lean tactics, unless their modules are
-- configured as Verbose.
/--
error: raw Lean tactic `We` at step 2 of exercise "example (p : Prop) (hp : p) : True ∧ p"; use a Lean Verbose tactic instead

Tactics can be allowed for a whole project with the option `goudlokje.allowedTactics`.

Note: This linter can be disabled with `set_option linter.goudlokje.rawTactic false`
-/
#guard_msgs in
example (p : Prop) (hp : p) : True ∧ p := by
  Let's first prove that True
  We finish
  Let's now prove that p
  We conclude by hp

set_option goudlokje.verboseModules "Verbose;; GoudlokjeTests.CustomTactic" in
#guard_msgs in
example : True ∧ True := by
  Let's first prove that True
  We finish
  Let's now prove that True
  We finish

-- Verbose tactics are not reported, although they expand to raw Lean tactics.
#guard_msgs in
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  Let's first prove that p
  We conclude by hp
  Let's now prove that q
  We conclude by hq

-- Proofs without Verbose are not checked at all.
#guard_msgs in
example : True ∧ True := by
  constructor
  · trivial
  · exact trivial

-- Raw tactics cannot be recorded as expected.
/--
error: raw Lean tactic `exact` at step 1 of exercise "documented raw tactic"; use a Lean Verbose tactic instead

Tactics can be allowed for a whole project with the option `goudlokje.allowedTactics`.

Note: This linter can be disabled with `set_option linter.goudlokje.rawTactic false`
---
error: `rawTactic` at step 1 of exercise "documented raw tactic" cannot be recorded as expected; remove it with `goudlokje update`

Note: This linter can be disabled with `set_option linter.goudlokje.rawTactic false`
-/
#guard_msgs in
Exercise "documented raw tactic"
  Given: (n : ℕ)
  Assume: (h : n = n)
  Conclusion: True
Proof:
  exact trivial
QED

/-! ## B2: type annotations -/

section
set_option linter.goudlokje.rawTactic false

/--
warning: `Fix` with a type annotation at step 2 of exercise "example : (∀ n : ℕ, n + 0 = n) ∧ True"

If this is intended, record it with `goudlokje update`.

Note: This linter can be disabled with `set_option linter.goudlokje.typeAscription false`
---
warning: type annotation `(trivial : True)` at step 5 of exercise "example : (∀ n : ℕ, n + 0 = n) ∧ True"

If this is intended, record it with `goudlokje update`.

Note: This linter can be disabled with `set_option linter.goudlokje.typeAscription false`
-/
#guard_msgs in
example : (∀ n : ℕ, n + 0 = n) ∧ True := by
  Let's first prove that ∀ n : ℕ, n + 0 = n
  Fix n : ℕ
  ring
  Let's now prove that True
  exact (trivial : True)

-- Binders, untyped `Fix` and Verbose statements are not type annotations.
#guard_msgs in
example : (∀ n : ℕ, n + 0 = n) ∧ ∃ k : ℕ, 4 = 2 * k := by
  Let's first prove that ∀ n : ℕ, n + 0 = n
  Fix n
  ring
  Let's now prove that ∃ k : ℕ, 4 = 2 * k
  Let's prove that 2 works
  rfl

-- Recorded annotations are not reported; recorded annotations that no longer occur are stale.
/--
warning: expected `typeAscription` at step 9 of exercise "documented annotation" no longer occurs; remove it with `goudlokje update`

Note: This linter can be disabled with `set_option linter.goudlokje.typeAscription false`
-/
#guard_msgs in
Exercise "documented annotation"
  Given: (n : ℕ)
  Assume: (h : n = n)
  Conclusion: True
Proof:
  exact (trivial : True)
QED

end

/-! ## B3: sorry -/

section
set_option linter.goudlokje.rawTactic false

-- `sorry` is an error, also when Lean's own warning is off (`warn.sorry false` above).
/--
error: `sorry` at step 2 of exercise "example : True ∧ True ∧ True"

If this exercise may contain `sorry`, allow it with `goudlokje update`.

Note: This linter can be disabled with `set_option linter.goudlokje.sorry false`
---
error: `sorry` at step 5 of exercise "example : True ∧ True ∧ True"

If this exercise may contain `sorry`, allow it with `goudlokje update`.

Note: This linter can be disabled with `set_option linter.goudlokje.sorry false`
---
error: `sorry` at step 7 of exercise "example : True ∧ True ∧ True"

If this exercise may contain `sorry`, allow it with `goudlokje update`.

Note: This linter can be disabled with `set_option linter.goudlokje.sorry false`
-/
#guard_msgs in
example : True ∧ True ∧ True := by
  Let's first prove that True
  sorry
  Let's now prove that True ∧ True
  Let's first prove that True
  exact sorry
  Let's now prove that True
  admit

-- Exercises can allow `sorry`; an allowance without any `sorry` is stale.
#guard_msgs in
Exercise "may contain sorry"
  Given: (n : ℕ)
  Assume: (h : n = n)
  Conclusion: 1 = 2
Proof:
  sorry
QED

/--
warning: exercise "stale allowance" allows `sorry` but contains none; remove `allowSorry` with `goudlokje update`

Note: This linter can be disabled with `set_option linter.goudlokje.sorry false`
-/
#guard_msgs in
Exercise "stale allowance"
  Given: (n : ℕ)
  Assume: (h : n = n)
  Conclusion: True
Proof:
  exact trivial
QED

end

/-
:::
-/
