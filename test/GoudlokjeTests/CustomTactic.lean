import Lean

/-! A Verbose-style tactic declared outside the `Verbose.*` modules, for testing
    `goudlokje.verboseModules` in `GoudlokjeTests.Lint`. -/

/-- Closes a goal of `True`. -/
macro "We " "finish" : tactic => `(tactic| trivial)
