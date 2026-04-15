import Goudlokje.Lint
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
  -- Lint the B1 fixture (raw tactics)
  let b1Results ← lintFile "TestSuite/Fixtures/LintB1.lean" (some cache)
  let b1 := b1Results.filter (·.check == "B1")
  unless b1.size ≥ 2 do
    throw (IO.userError
      s!"testAllLintChecks [B1]: expected ≥2 B1 violations, got {b1.size}")
  unless b1.any (fun r => (r.message.splitOn "constructor").length > 1) do
    throw (IO.userError
      "testAllLintChecks [B1]: expected message mentioning 'constructor'")
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

/-- `classifyLint` correctly classifies expected, unexpected, and stale lint violations. -/
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
  -- B1@line1 should be classified as expected.
  unless cr.violations.any (fun v => match v with | .expected r => r.line == 1 && r.check == "B1" | _ => false) do
    throw (IO.userError "testClassifyLint: B1@line1 should be 'expected'")
  -- B3@line2 should be classified as unexpected.
  unless cr.violations.any (fun v => match v with | .unexpected r => r.line == 2 && r.check == "B3" | _ => false) do
    throw (IO.userError "testClassifyLint: B3@line2 should be 'unexpected'")
  -- No stale entries (the documented B1@line1 is still present).
  unless cr.stale.isEmpty do
    throw (IO.userError s!"testClassifyLint: expected no stale entries, got {cr.stale.size}")

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

def runAll : IO Unit := do
  testAllLintChecks
  IO.println "  ✓ testAllLintChecks"
  testClassifyLint
  IO.println "  ✓ testClassifyLint"
  testClassifyLintStale
  IO.println "  ✓ testClassifyLintStale"

end TestSuite.Lint
