import Goudlokje.Linter.Explain
import Verbose.English.All

/-! Tests for step extraction and goal chains, via the explain linter. -/

set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.goudlokje.explain true

-- Verbose step boundaries start new chains; `show` continues the chain of the goal it changes.
/--
warning: exercise "example : 1 + 1 = 2 ∧ 2 + 2 = 4":
  step 1: tacticLet'sFirstProveThat_ [verbose, chain 0]
  step 2: Lean.Parser.Tactic.show [chain 1]
  step 3: Mathlib.Tactic.normNum [closes]
  step 4: tacticLet'sNowProveThat_ [verbose, chain 2]
  step 5: Lean.Parser.Tactic.show [chain 2]
  step 6: Mathlib.Tactic.normNum [closes]

Note: This linter can be disabled with `set_option linter.goudlokje.explain false`
-/
#guard_msgs in
example : 1 + 1 = 2 ∧ 2 + 2 = 4 := by
  Let's first prove that 1 + 1 = 2
  show 1 + 1 = 2
  norm_num
  Let's now prove that 2 + 2 = 4
  show 2 + 2 = 4
  norm_num

-- The Verbose `Exercise` wrapper is not a step; the exercise title is used as its name.
/--
warning: exercise "wrapper":
  step 1: Lean.Parser.Tactic.show [chain 0]
  step 2: Mathlib.Tactic.normNum [closes]

Note: This linter can be disabled with `set_option linter.goudlokje.explain false`
-/
#guard_msgs in
Exercise "wrapper"
  Given: (n : ℕ)
  Assume: (h : n = n)
  Conclusion: 1 + 1 = 2
Proof:
  show 1 + 1 = 2
  norm_num
QED

-- Focusing bullets are not steps, the tactics inside them are. Named declarations are named after
-- the declaration.
/--
warning: exercise "twoGoals":
  step 1: Lean.Parser.Tactic.constructor [chain 0]
  step 2: Lean.Parser.Tactic.show [chain 1]
  step 3: Lean.Parser.Tactic.tacticRfl [closes]
  step 4: Lean.Parser.Tactic.tacticRfl [closes]

Note: This linter can be disabled with `set_option linter.goudlokje.explain false`
-/
#guard_msgs in
theorem twoGoals : 1 + 1 = 2 ∧ 2 + 2 = 4 := by
  constructor
  · show 1 + 1 = 2
    rfl
  · rfl

-- Macro expansions (here of the Verbose `We conclude by`) are not steps. Anonymous examples are
-- named after their statement.
/--
warning: exercise "example (p q : Prop) (hp : p) (hq : q) : p ∧ q":
  step 1: tacticLet'sFirstProveThat_ [verbose, chain 0]
  step 2: tacticWeConcludeBy_ [verbose, closes]
  step 3: tacticLet'sNowProveThat_ [verbose, chain 1]
  step 4: tacticWeConcludeBy_ [verbose, closes]

Note: This linter can be disabled with `set_option linter.goudlokje.explain false`
-/
#guard_msgs in
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  Let's first prove that p
  We conclude by hp
  Let's now prove that q
  We conclude by hq

-- Steps are numbered by position: blank lines and comments in between do not count.
/--
warning: exercise "example : 1 + 1 = 2 ∧ 2 + 2 = 4":
  step 1: tacticLet'sFirstProveThat_ [verbose, chain 0]
  step 2: Mathlib.Tactic.normNum [closes]
  step 3: tacticLet'sNowProveThat_ [verbose, chain 1]
  step 4: Mathlib.Tactic.normNum [closes]

Note: This linter can be disabled with `set_option linter.goudlokje.explain false`
-/
#guard_msgs in
example : 1 + 1 = 2 ∧ 2 + 2 = 4 := by
  Let's first prove that 1 + 1 = 2

  -- A comment.
  norm_num
  Let's now prove that 2 + 2 = 4

  norm_num
