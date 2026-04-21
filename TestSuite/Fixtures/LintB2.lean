-- Fixture for CheckB2 (type annotation detection) tests.
-- Contains type annotations in Verbose proof bodies that CheckB2 should flag.
import Verbose.English.All

set_option linter.unusedTactic false

-- Fix with explicit type annotation inside a Verbose proof:
-- CheckB2 should flag the `Fix n : ℕ` line.
example : (∀ n : ℕ, n + 0 = n) ∧ True := by
  Let's first prove that ∀ n : ℕ, n + 0 = n
  Fix n : ℕ
  ring
  Let's now prove that True
  trivial

-- Type-cast annotation `(expr : T)` in a Verbose proof:
-- CheckB2 should flag `(trivial : True)`.
example : True ∧ True := by
  Let's first prove that True
  exact (trivial : True)
  Let's now prove that True
  trivial
