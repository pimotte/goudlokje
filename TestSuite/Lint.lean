import Goudlokje.Lint
import Goudlokje.ProbeWorker
import Goudlokje.TestFile

namespace TestSuite.Lint

open Goudlokje

/-- Run all lint checks using a shared env cache.

    The cache is still needed: all three fixture files (`LintB1.lean`,
    `LintB2.lean`, `LintB3.lean`) share the same `import Verbose.English.All`
    header.  Building the Lean environment for that import (which transitively
    pulls in Mathlib) is the dominant cost of each `lintFile` call.  Without
    the cache, `processHeader` would run once per fixture — three times total —
    for identical imports.  The shared `EnvCache` ensures the environment is
    built exactly once and reused for the remaining two calls. -/
def testAllLintChecks : IO Unit := do
  let cache ← mkEnvCache
  -- B1 does NOT fire on regular (non-Verbose) Lean proofs.
  let b1Results ← lintFile "TestSuite/Fixtures/LintB1.lean" (some cache)
  let b1 := b1Results.filter (·.check == "B1")
  unless b1.size == 0 do
    throw (IO.userError
      s!"testAllLintChecks [B1]: expected 0 B1 violations on regular proof, got {b1.size}")
  -- B1 DOES fire on Verbose Lean proofs with raw tactics.
  let b1VerboseResults ← lintFile "TestSuite/Fixtures/LintB1VerboseCheck.lean" (some cache)
  let b1Verbose := b1VerboseResults.filter (·.check == "B1")
  unless b1Verbose.size ≥ 2 do
    throw (IO.userError
      s!"testAllLintChecks [B1Verbose]: expected ≥2 B1 violations in Verbose proof, got {b1Verbose.size}")
  unless b1Verbose.any (fun r => (r.message.splitOn "exact").length > 1) do
    throw (IO.userError
      "testAllLintChecks [B1Verbose]: expected message mentioning 'exact'")
  -- B3 must be empty for the B1 fixture (no sorry)
  let b3inB1 := b1Results.filter (·.check == "B3")
  unless b3inB1.isEmpty do
    throw (IO.userError
      s!"testAllLintChecks [B1/B3]: unexpected B3 in LintB1 fixture, got {b3inB1.size}")
  -- Lint the B3 fixture (sorry)
  let b3Results ← lintFile "TestSuite/Fixtures/LintB3.lean" (some cache)
  let b3 := b3Results.filter (·.check == "B3")
  unless b3.size ≥ 1 do
    throw (IO.userError
      s!"testAllLintChecks [B3]: expected ≥1 B3 violation, got {b3.size}")
  unless b3.any (fun r => (r.message.splitOn "sorry").length > 1) do
    throw (IO.userError
      "testAllLintChecks [B3]: expected message mentioning 'sorry'")
  -- B1 must be empty for the B3 fixture (sorry expands to exact, but is excluded)
  let b1inB3 := b3Results.filter (·.check == "B1")
  unless b1inB3.isEmpty do
    throw (IO.userError
      s!"testAllLintChecks [B3/B1]: sorry expansion must not produce B1, got {b1inB3.size}")
  -- Lint the B2 fixture (type annotations)
  let b2Results ← lintFile "TestSuite/Fixtures/LintB2.lean" (some cache)
  let b2 := b2Results.filter (·.check == "B2")
  unless b2.size ≥ 1 do
    throw (IO.userError
      s!"testAllLintChecks [B2]: expected ≥1 B2 violation, got {b2.size}")
  -- No two B2 violations at the same position (deduplication works)
  for i in List.range b2.size do
    for j in List.range b2.size do
      if i < j then
        let ri := b2[i]!
        let rj := b2[j]!
        if ri.line == rj.line && ri.column == rj.column then
          throw (IO.userError
            s!"testAllLintChecks [B2 dedup]: duplicate at {ri.line}:{ri.column}")

/-- `classifyLint` correctly classifies expected, unexpected, and stale lint violations.
    B1 violations are always unexpected (cannot be suppressed via test.json).
    B1 entries in test.json are always stale (B1 cannot be documented). -/
def testClassifyLint : IO Unit := do
  let violations : Array LintResult := #[
    { file := "a.lean", line := 1, column := 0, check := "B1", message := "Raw Lean tactic 'exact'" },
    { file := "a.lean", line := 2, column := 0, check := "B3", message := "sorry in proof body" }
  ]
  -- B1 at line 1 is documented; B3 at line 2 is not.
  let tf : TestFile := { expected := #[], lint := #[
    { file := "a.lean", line := 1, column := 0, check := "B1", message := "Raw Lean tactic 'exact'" }
  ]}
  let cr := classifyLint violations tf
  -- B1@line1 should always be classified as unexpected (B1 cannot be suppressed via test.json).
  unless cr.violations.any (fun v => match v with | .unexpected r => r.line == 1 && r.check == "B1" | _ => false) do
    throw (IO.userError "testClassifyLint: B1@line1 should be 'unexpected' (B1 cannot be suppressed)")
  -- B3@line2 should be classified as unexpected.
  unless cr.violations.any (fun v => match v with | .unexpected r => r.line == 2 && r.check == "B3" | _ => false) do
    throw (IO.userError "testClassifyLint: B3@line2 should be 'unexpected'")
  -- The documented B1@line1 entry should appear as stale (B1 entries cannot be documented).
  unless cr.stale.any (fun s => s.entry.check == "B1" && s.entry.line == 1) do
    throw (IO.userError "testClassifyLint: B1@line1 TestFile entry should be stale (B1 cannot be documented)")

/-- `classifyLint` detects stale lint entries whose violation no longer occurs. -/
def testClassifyLintStale : IO Unit := do
  let violations : Array LintResult := #[]
  let tf : TestFile := { expected := #[], lint := #[
    { file := "a.lean", line := 3, column := 0, check := "B2", message := "Fix with annotation" }
  ]}
  let cr := classifyLint violations tf
  unless cr.stale.size == 1 do
    throw (IO.userError s!"testClassifyLintStale: expected 1 stale entry, got {cr.stale.size}")
  unless cr.stale[0]!.entry.check == "B2" do
    throw (IO.userError "testClassifyLintStale: stale entry should be B2")

/-- Regression: Verbose step-boundary lines starting with "Let's" or "Since" must
    not produce any B1 violations, even though they expand internally to raw Lean
    tactics such as `constructor` or `exact`. -/
def testB1NoFalsePositivesOnVerboseLines : IO Unit := do
  let cache ← mkEnvCache
  let results ← lintFile "TestSuite/Fixtures/LintB1Verbose.lean" (some cache)
  let b1 := results.filter (·.check == "B1")
  unless b1.isEmpty do
    let msgs := b1.map (fun r => s!"{r.line}:{r.column} {r.message}")
    throw (IO.userError
      s!"testB1NoFalsePositivesOnVerboseLines: expected 0 B1 violations on Verbose file, got {b1.size}: {msgs}")

/-- Regression: a Verbose proof with no user-written (expr : T) ascriptions must
    produce zero B2 violations (no false positives from internal Lean elaboration). -/
def testB2NoFalsePositivesOnVerboseProofs : IO Unit := do
  let cache ← mkEnvCache
  let results ← lintFile "TestSuite/Fixtures/LintB2FalsePositive.lean" (some cache)
  let b2 := results.filter (·.check == "B2")
  unless b2.isEmpty do
    let msgs := b2.map (fun r => s!"{r.line}:{r.column} {r.message}")
    throw (IO.userError
      s!"testB2NoFalsePositivesOnVerboseProofs: expected 0 B2 violations, got {b2.size}: {msgs}")

/-- `lintFileIsolated` must produce the same B3 violations as the direct `lintFile` call. -/
def testLintFileIsolatedMatchesDirectCall : IO Unit := do
  let direct ← lintFile "TestSuite/Fixtures/LintB3.lean" none
  let isolated ← lintFileIsolated "TestSuite/Fixtures/LintB3.lean"
  unless direct.size == isolated.size do
    throw (IO.userError
      s!"testLintFileIsolatedMatchesDirectCall: direct={direct.size} isolated={isolated.size}")
  for r in direct do
    unless isolated.any (fun s => s.file == r.file && s.line == r.line &&
                                   s.column == r.column && s.check == r.check) do
      throw (IO.userError
        s!"testLintFileIsolatedMatchesDirectCall: {r.check}@{r.line}:{r.column} missing from isolated results")

/-- B1 violations are always unexpected even when present in a test file with matching entries. -/
def testB1AlwaysUnexpectedInClassify : IO Unit := do
  let violations : Array LintResult := #[
    { file := "x.lean", line := 5, column := 2, check := "B1", message := "Raw Lean tactic 'exact'" }
  ]
  let tf : TestFile := { expected := #[], lint := #[
    { file := "x.lean", line := 5, column := 2, check := "B1", message := "Raw Lean tactic 'exact'" }
  ]}
  let cr := classifyLint violations tf
  unless cr.violations.all (fun v => match v with | .unexpected _ => true | .expected _ => false) do
    throw (IO.userError "testB1AlwaysUnexpected: B1 violation should always be 'unexpected'")
  unless cr.stale.any (fun s => s.entry.check == "B1") do
    throw (IO.userError "testB1AlwaysUnexpected: matching B1 TestFile entry should be stale")

def runAll : IO Unit := do
  testAllLintChecks
  IO.println "  ✓ testAllLintChecks"
  testClassifyLint
  IO.println "  ✓ testClassifyLint"
  testClassifyLintStale
  IO.println "  ✓ testClassifyLintStale"
  testB1NoFalsePositivesOnVerboseLines
  IO.println "  ✓ testB1NoFalsePositivesOnVerboseLines"
  testB2NoFalsePositivesOnVerboseProofs
  IO.println "  ✓ testB2NoFalsePositivesOnVerboseProofs"
  testLintFileIsolatedMatchesDirectCall
  IO.println "  ✓ testLintFileIsolatedMatchesDirectCall"
  testB1AlwaysUnexpectedInClassify
  IO.println "  ✓ testB1AlwaysUnexpectedInClassify"

end TestSuite.Lint
