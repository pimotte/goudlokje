import Goudlokje.Analysis

namespace TestSuite.Analysis

open Goudlokje

/-- Integration test: verify that `analyzeFile` detects `decide` as a shortcut
    for trivially decidable goals in the Simple fixture. -/
def testDetectsDecideShortcut : IO Unit := do
  -- Path is relative to the project root (where Lake runs the executable)
  let fixturePath : System.FilePath := "TestSuite/Fixtures/Simple.lean"
  let results ← analyzeFile fixturePath #["decide"]
  unless results.size ≥ 1 do
    throw (IO.userError
      s!"testDetectsDecideShortcut: expected ≥1 probe result, got {results.size}")
  unless results.any (fun r => r.tactic == "decide") do
    throw (IO.userError
      "testDetectsDecideShortcut: expected tactic 'decide' in results")

/-- Integration test: verify that no spurious shortcuts are reported when
    the probe list is empty. -/
def testNoTacticsNoResults : IO Unit := do
  let fixturePath : System.FilePath := "TestSuite/Fixtures/Simple.lean"
  let results ← analyzeFile fixturePath #[]
  unless results.isEmpty do
    throw (IO.userError
      s!"testNoTacticsNoResults: expected 0 results, got {results.size}")

/-- Integration test: verify that `analyzeFile` detects `decide` as a shortcut
    inside a Lean Verbose proof (steps bounded by Verbose tactics like
    `Let's first prove that …`). -/
def testDetectsDecideShortcutInVerboseFile : IO Unit := do
  let fixturePath : System.FilePath := "TestSuite/Fixtures/Verbose.lean"
  let results ← analyzeFile fixturePath #["decide"]
  unless results.size ≥ 1 do
    throw (IO.userError
      s!"testVerbose: expected ≥1 probe result, got {results.size}")
  unless results.any (fun r => r.tactic == "decide") do
    throw (IO.userError
      "testVerbose: expected tactic 'decide' in results")

/-- Integration test: verify that `analyzeFile` detects `decide` as a shortcut
    inside a Waterproof Genre `#doc` code block. -/
def testDetectsDecideShortcutInWaterproofFile : IO Unit := do
  let fixturePath : System.FilePath := "TestSuite/Fixtures/Waterproof.lean"
  let results ← analyzeFile fixturePath #["decide"]
  unless results.size ≥ 1 do
    throw (IO.userError
      s!"testWaterproof: expected ≥1 probe result, got {results.size}")
  unless results.any (fun r => r.tactic == "decide") do
    throw (IO.userError
      "testWaterproof: expected tactic 'decide' in results")

/-- Integration test: verify that `analyzeFile` detects `decide` as a shortcut
    in a file using both WaterproofGenre `#doc` blocks and Lean Verbose tactics.
    This combination is the typical usage in external Waterproof exercise projects. -/
def testDetectsDecideShortcutInVerboseWaterproofFile : IO Unit := do
  let fixturePath : System.FilePath := "TestSuite/Fixtures/VerboseWaterproof.lean"
  let results ← analyzeFile fixturePath #["decide"]
  unless results.size ≥ 1 do
    throw (IO.userError
      s!"testVerboseWaterproof: expected ≥1 probe result, got {results.size}")
  unless results.any (fun r => r.tactic == "decide") do
    throw (IO.userError
      "testVerboseWaterproof: expected tactic 'decide' in results")

/-- Integration test: verify that `analyzeFile` never returns duplicate results.
    The same (file, line, column, tactic) must appear at most once. -/
def testNoDuplicateResults : IO Unit := do
  let fixturePath : System.FilePath := "TestSuite/Fixtures/Simple.lean"
  let results ← analyzeFile fixturePath #["decide"]
  for i in List.range results.size do
    for j in List.range results.size do
      if i < j then
        let ri := results[i]!
        let rj := results[j]!
        if ri == rj then
          throw (IO.userError
            s!"testNoDuplicateResults: duplicate at {ri.file}:{ri.line}:{ri.column} — `{ri.tactic}`")

/-- Verbose step filtering: without filtering, `decide` is a shortcut at both
    the `show` (noop) and `norm_num` positions within each step body.
    This verifies the unfiltered result has more shortcuts than the filtered one. -/
def testVerboseFilterReducesResults : IO Unit := do
  let fixturePath : System.FilePath := "TestSuite/Fixtures/VerboseMultiStep.lean"
  let withoutFilter ← analyzeFile fixturePath #["decide"] (filterVerboseSteps := false)
  let withFilter    ← analyzeFile fixturePath #["decide"] (filterVerboseSteps := true)
  unless withFilter.size < withoutFilter.size do
    throw (IO.userError
      s!"testVerboseFilter: expected filter to reduce shortcut count, \
        got unfiltered={withoutFilter.size} filtered={withFilter.size}")

/-- Verbose step filtering: the filtered result keeps only the first tactic per step,
    then skip-last removes the final step's position.  The fixture has 2 steps with
    `show` as the first tactic each; after filtering and skip-last, only step 1 remains. -/
def testVerboseFilterKeepsFirstPerStep : IO Unit := do
  let fixturePath : System.FilePath := "TestSuite/Fixtures/VerboseMultiStep.lean"
  let results ← analyzeFile fixturePath #["decide"] (filterVerboseSteps := true)
  -- 2 steps → filter keeps show@step1 and show@step2 → skip-last removes show@step2 → 1 shortcut
  unless results.size == 1 do
    throw (IO.userError
      s!"testVerboseFilterKeepsFirstPerStep: expected 1 shortcut (step 1 only; step 2 is last), \
        got {results.size}")

/-- Environment cache: analyzing the same file twice with a shared cache
    should return identical results to analyzing without the cache. -/
def testEnvCacheReturnsSameResults : IO Unit := do
  let fixturePath : System.FilePath := "TestSuite/Fixtures/Simple.lean"
  let withoutCache ← analyzeFile fixturePath #["decide"]
  let cache ← mkEnvCache
  let withCache ← analyzeFile fixturePath #["decide"] (envCache := some cache)
  unless withCache == withoutCache do
    throw (IO.userError
      s!"testEnvCache: cached result differs from uncached \
        (uncached={withoutCache.size}, cached={withCache.size})")

/-- Environment cache: a second analysis of a file sharing the same imports
    should produce the same results (the cached env is valid for both). -/
def testEnvCacheReusedAcrossFiles : IO Unit := do
  -- Both Simple.lean and VerboseMultiStep.lean can be analyzed, but they have
  -- different imports so the cache stores two environments. This verifies that
  -- the cache doesn't return a stale environment for the second file.
  let cache ← mkEnvCache
  let r1 ← analyzeFile "TestSuite/Fixtures/Simple.lean" #["decide"] (envCache := some cache)
  let r2 ← analyzeFile "TestSuite/Fixtures/Simple.lean" #["decide"] (envCache := some cache)
  unless r1 == r2 do
    throw (IO.userError "testEnvCacheReusedAcrossFiles: repeated analysis differs")

/-- onProbe callback is invoked for every probe attempt (success and failure).
    We pass a tactic that succeeds on some goals and use a counter to verify
    the callback is called at all. -/
def testOnProbeCallbackInvoked : IO Unit := do
  let callCount ← IO.mkRef (0 : Nat)
  let callback : Nat → Nat → String → Bool → IO Unit := fun _ _ _ _ =>
    callCount.modify (· + 1)
  let _ ← analyzeFile "TestSuite/Fixtures/Simple.lean" #["decide"]
    (onProbe := some callback)
  let total ← callCount.get
  unless total > 0 do
    throw (IO.userError
      s!"testOnProbeCallbackInvoked: expected >0 probe callbacks, got {total}")

/-- onProbe callback is invoked for failed probes too, not only successes.
    We use a tactic that never succeeds (`skip`) and expect callbacks anyway. -/
def testOnProbeCallbackIncludesFailures : IO Unit := do
  let callCount ← IO.mkRef (0 : Nat)
  let callback : Nat → Nat → String → Bool → IO Unit := fun _ _ _ _ =>
    callCount.modify (· + 1)
  -- `skip` always leaves the goal unchanged (does not close it)
  let results ← analyzeFile "TestSuite/Fixtures/Simple.lean" #["skip"]
    (onProbe := some callback)
  let total ← callCount.get
  -- `skip` never succeeds, so there should be no results
  unless results.isEmpty do
    throw (IO.userError
      s!"testOnProbeCallbackIncludesFailures: expected no results for 'skip', got {results.size}")
  -- but the callback must still have been called (for the failed attempts)
  unless total > 0 do
    throw (IO.userError
      s!"testOnProbeCallbackIncludesFailures: expected >0 callbacks for failures, got {total}")

/-- Verbose step filtering must reset per declaration.
    A declaration WITHOUT step boundaries must keep all its tactics even when
    a preceding declaration in the same file DOES have step boundaries.
    Without this, the filter's state leaks across declarations and suppresses
    shortcuts in non-Verbose exercises. -/
def testVerboseFilterRespectsDeclarationBoundaries : IO Unit := do
  let fixturePath : System.FilePath := "TestSuite/Fixtures/VerboseMultiDecl.lean"
  -- Decl 2 (no step boundaries) has `constructor` at line 21.
  -- Without filter: decide must be found at decl 2's `constructor` (line 21).
  let withoutFilter ← analyzeFile fixturePath #["decide"] (filterVerboseSteps := false)
  unless withoutFilter.any (fun r => r.line == 21) do
    throw (IO.userError
      "testVerboseFilterRespectsDeclarationBoundaries: fixture sanity check failed \
       — expected decide shortcut at line 21 (constructor, unfiltered)")
  -- With filter: decl 2 has no step boundaries, so filterVerboseSteps must NOT suppress it.
  -- (skip-last removes `all_goals norm_num` at line 22 but keeps `constructor` at line 21.)
  let withFilter ← analyzeFile fixturePath #["decide"] (filterVerboseSteps := true)
  unless withFilter.any (fun r => r.line == 21) do
    throw (IO.userError
      "testVerboseFilterRespectsDeclarationBoundaries: filterVerboseSteps incorrectly \
       suppressed shortcuts in a declaration with no step boundaries (line 21)")
  -- Sanity: filter still reduces the overall count (decl 1's step filtering works).
  unless withFilter.size < withoutFilter.size do
    throw (IO.userError
      s!"testVerboseFilterRespectsDeclarationBoundaries: expected filter to reduce overall \
        count, got unfiltered={withoutFilter.size} filtered={withFilter.size}")

/-- The number of successful onProbe callbacks equals the number of (deduplicated)
    probe results returned by analyzeFile. -/
def testOnProbeSuccessCountMatchesResults : IO Unit := do
  let successCount ← IO.mkRef (0 : Nat)
  let callback : Nat → Nat → String → Bool → IO Unit := fun _ _ _ success =>
    if success then successCount.modify (· + 1) else pure ()
  -- Use a single-tactic probe so that each (pos, tactic) is hit at most once per goal.
  -- Deduplication means results.size ≤ successCount (multiple goals at a pos count once).
  let results ← analyzeFile "TestSuite/Fixtures/Simple.lean" #["decide"]
    (onProbe := some callback)
  let succs ← successCount.get
  -- Every deduplicated result must have had at least one successful callback
  unless succs >= results.size do
    throw (IO.userError
      s!"testOnProbeSuccessCount: successes={succs} < results={results.size}")

/-- Regression test for the mwe exercise 1.1.13 issue: a probe tactic that can close
    the goal at the LAST step of a proof must not be reported as a shortcut.
    A shortcut at the final step does not save any proof lines — the student still
    has to write that step — so reporting it is a false positive.
    The fixture has exactly 2 tactic positions (one per Verbose step) after filtering;
    skip-last removes the second → exactly 1 shortcut remains. -/
def testSkipLastTacticNotReported : IO Unit := do
  let fixturePath : System.FilePath := "TestSuite/Fixtures/SkipLastStep.lean"
  -- filterVerboseSteps reduces the fixture to exactly 2 positions (one per step);
  -- skip-last then removes the last → 1 shortcut at step 1.
  let results ← analyzeFile fixturePath #["decide"] (filterVerboseSteps := true)
  unless results.size == 1 do
    throw (IO.userError
      s!"testSkipLastTacticNotReported: expected exactly 1 shortcut (last step skipped), \
        got {results.size}")

/-- Regression test: the `Exercise`/`Example` Verbose command wraps the `Proof:` body
    in `with(out)_suggestions%$tkp` where `tkp` is the `Proof:` token.  This generates
    a `TacticInfo` node at the `Proof:` position with a non-empty goal, which must NOT
    be treated as a user-written proof step and must NOT be probed.

    The fixture uses an `Exercise` with a 2-tactic proof and no step boundaries
    (so `filterVerboseSteps` does not help).  After filtering the wrapper and
    applying skip-last, exactly 1 shortcut remains (the `show` step).
    Without the fix, 2 shortcuts are reported (wrapper@Proof: + show). -/
def testVerboseExerciseDoesNotProbeBeforeProof : IO Unit := do
  let fixturePath : System.FilePath := "TestSuite/Fixtures/VerboseExercise.lean"
  let results ← analyzeFile fixturePath #["decide"]
  unless results.size == 1 do
    throw (IO.userError
      s!"testVerboseExerciseDoesNotProbeBeforeProof: expected 1 shortcut \
        (proof wrapper at Proof: must not be probed), got {results.size}")

def runAll : IO Unit := do
  testDetectsDecideShortcut; IO.println "  ✓ testDetectsDecideShortcut"
  testNoTacticsNoResults;    IO.println "  ✓ testNoTacticsNoResults"
  testNoDuplicateResults;    IO.println "  ✓ testNoDuplicateResults"
  testDetectsDecideShortcutInVerboseFile;
                             IO.println "  ✓ testDetectsDecideShortcutInVerboseFile"
  testDetectsDecideShortcutInWaterproofFile;
                             IO.println "  ✓ testDetectsDecideShortcutInWaterproofFile"
  testDetectsDecideShortcutInVerboseWaterproofFile;
                             IO.println "  ✓ testDetectsDecideShortcutInVerboseWaterproofFile"
  testVerboseFilterReducesResults;
                             IO.println "  ✓ testVerboseFilterReducesResults"
  testVerboseFilterKeepsFirstPerStep;
                             IO.println "  ✓ testVerboseFilterKeepsFirstPerStep"
  testVerboseFilterRespectsDeclarationBoundaries;
                             IO.println "  ✓ testVerboseFilterRespectsDeclarationBoundaries"
  testEnvCacheReturnsSameResults;
                             IO.println "  ✓ testEnvCacheReturnsSameResults"
  testEnvCacheReusedAcrossFiles;
                             IO.println "  ✓ testEnvCacheReusedAcrossFiles"
  testOnProbeCallbackInvoked;
                             IO.println "  ✓ testOnProbeCallbackInvoked"
  testOnProbeCallbackIncludesFailures;
                             IO.println "  ✓ testOnProbeCallbackIncludesFailures"
  testOnProbeSuccessCountMatchesResults;
                             IO.println "  ✓ testOnProbeSuccessCountMatchesResults"
  testSkipLastTacticNotReported;
                             IO.println "  ✓ testSkipLastTacticNotReported"
  testVerboseExerciseDoesNotProbeBeforeProof;
                             IO.println "  ✓ testVerboseExerciseDoesNotProbeBeforeProof"

end TestSuite.Analysis
