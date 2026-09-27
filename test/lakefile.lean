import Lake
open Lake DSL

/-! Tests of Goudlokje. They check worksheets written with Lean Verbose and the Waterproof genre,
    which Goudlokje itself does not depend on, so they are a separate package. -/

package goudlokjeTest

require "goudlokje" from ".."
require "waterproof-genre"
      from git "https://github.com/impermeable/waterproof-genre" @ "feature/smaller-genre"
require "verbose-lean4"
      from git "https://github.com/PatrickMassot/verbose-lean4" @ "v4.31.0"

/-- Tests of the linters, run with `lake test`: every module is a test file whose checks
    (`#guard_msgs`, `#guard`) fail the build when they fail. -/
@[default_target, test_driver]
lean_lib "GoudlokjeTests" where
  globs := #[.submodules `GoudlokjeTests]

/-! The end-to-end test `e2e/run.sh` copies worksheets to `e2e/work` and checks them as the
    following libraries. -/

/-- The worksheet used to test the `check` and `update` commands. -/
lean_lib E2EWorksheets where
  srcDir := "e2e/work"
  globs := #[.submodules `Worksheets]
  leanOptions := #[
    ⟨`weak.goudlokje.probes, "decide;; norm_num"⟩,
    ⟨`weak.goudlokje.allowedTactics, "show;; norm_num"⟩
  ]

/-- Regression fixtures, checked with the probes the project used before the linter refactor. -/
lean_lib E2EFixtures where
  srcDir := "e2e/work"
  globs := #[.submodules `Fixtures]
  leanOptions := #[⟨`weak.goudlokje.probes, "decide;; tauto;; omega;; norm_num;; simp;; ring"⟩]
