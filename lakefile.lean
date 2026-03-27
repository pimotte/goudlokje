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

-- Build fixture files so their package dependencies (Verbose, WaterproofGenre) are compiled.
-- These oleans must be present at runtime when `analyzeFile` processes the fixture files.
@[default_target]
lean_lib "TestFixtures" where
  roots := #[`TestSuite.Fixtures.Simple, `TestSuite.Fixtures.Verbose,
             `TestSuite.Fixtures.VerboseMultiStep, `TestSuite.Fixtures.SkipLastStep,
             `TestSuite.Fixtures.VerboseExercise, `TestSuite.Fixtures.VerboseMultiDecl,
             `TestSuite.Fixtures.VerboseExerciseWithSteps,
             `TestSuite.Fixtures.Waterproof, `TestSuite.Fixtures.VerboseWaterproof]

-- FixtureDeps imports Verbose and Waterproof packages so their oleans are compiled.
-- This ensures `analyzeFile` can import them at runtime when processing fixture files.
@[default_target]
lean_lib "FixtureDeps" where
  roots := #[`FixtureDeps]

lean_exe "goudlokje_tests" where
  root := `TestSuite.Main
  moreLinkArgs := #["-rdynamic"]

require "leanprover" / "lean4-cli" @ git "v4.29.0-rc6"
require "waterproof-genre"
      from git "https://github.com/impermeable/waterproof-genre" @ "feature/smaller-genre"
require "verbose-lean4"
      from git "https://github.com/impermeable/verbose-lean4" @ "update/v4.29.0-rc6"
