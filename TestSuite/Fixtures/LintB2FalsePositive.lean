-- Fixture for CheckB2 false-positive regression tests.
-- This file contains NO user-written (expr : T) type-cast ascriptions in proof
-- bodies, so CheckB2 should report ZERO violations.
-- Regression guard for internally-synthesised typeAscription info-tree nodes that
-- are not written by the user (e.g. from Lean/Verbose internal elaboration).
import Verbose.English.All

set_option linter.unusedTactic false

-- Theorem statement contains (n : ℕ) in the return type; this must NOT be
-- flagged since it is part of the declaration header, not a proof-body ascription.
example : ∀ n : ℕ, n + 0 = n := by
  Fix n
  ring

-- Existential proof using Verbose witness tactic; no user-written ascription.
example : ∃ k : ℕ, 4 = 2 * k := by
  Let's prove that 2 works
  rfl

-- Conjunction proof with Verbose step boundaries; no ascriptions.
example : 1 + 1 = 2 ∧ 2 + 2 = 4 := by
  Let's first prove that 1 + 1 = 2
  norm_num
  Let's now prove that 2 + 2 = 4
  norm_num
