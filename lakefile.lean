import Lake
open Lake DSL

/-! Goudlokje depends only on Lean and, for its command-line interface, `Cli`. The tests, which need
    Lean Verbose and the Waterproof genre, are a separate package in `test/`. -/

package "goudlokje" where
  version := v!"0.1.0"

@[default_target]
lean_lib "Goudlokje" where
  globs := #[.andSubmodules `Goudlokje]

@[default_target]
lean_exe "goudlokje" where
  root := `Main

require "leanprover" / "lean4-cli" @ git "v4.31.0"

/-- Runs the unit tests of the test package (`test/lakefile.lean`) with `lake test`. -/
@[test_driver]
script test (args) do
  let child ← IO.Process.spawn { cmd := "lake", args := #["test", "--"] ++ args.toArray, cwd := "test" }
  child.wait
