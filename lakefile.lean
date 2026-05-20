import Lake
open Lake DSL

package "goudlokje" where
  version := v!"0.1.0"

lean_lib "Goudlokje" where
  roots := #[`Goudlokje]

@[default_target]
lean_exe "goudlokje" where
  root := `Main
  moreLinkArgs := #["-rdynamic"]

lean_lib "TestSuite" where
  roots := #[`TestSuite]

-- FixtureDeps imports Verbose and Waterproof packages so their oleans are compiled.
-- This ensures `analyzeFile` can import them at runtime when processing fixture files.
@[default_target]
lean_lib "FixtureDeps" where
  roots := #[`FixtureDeps]

lean_exe "goudlokje_tests" where
  root := `TestSuite.Main
  moreLinkArgs := #["-rdynamic"]

lean_exe "debug_analysis" where
  root := `DebugAnalysis
  moreLinkArgs := #["-rdynamic"]

require "leanprover" / "lean4-cli" @ git "v4.29.0-rc6"
require "waterproof-genre"
      from git "https://github.com/impermeable/waterproof-genre" @ "feature/smaller-genre"
require "verbose-lean4"
      from git "https://github.com/impermeable/verbose-lean4" @ "update/v4.29.0-rc6"
