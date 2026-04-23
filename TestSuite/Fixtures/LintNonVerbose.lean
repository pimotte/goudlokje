-- Fixture: non-Verbose proofs that must NOT trigger B2 or B3 after issue #13.
-- Verifies that B2 and B3 are restricted to Verbose Lean proofs only.

set_option warn.sorry false

-- sorry in a non-Verbose proof: must not trigger B3.
example : True := by
  sorry

-- type ascription in a non-Verbose proof: must not trigger B2.
example : True ∧ True := by
  exact And.intro (trivial : True) trivial
