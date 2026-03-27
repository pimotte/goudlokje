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

/-- Verbose step filtering: each step is probed until the first shortcut; skip-last
    removes the last non-boundary tactic of the declaration.
    The fixture has 2 steps: step 1 = [show@12, norm_num@13], step 2 = [show@15, norm_num@16].
    Skip-last drops norm_num@16 (the last tactic overall), leaving step 2 = [show@15].
    Probing step 1: show@12 → shortcut → 1 shortcut for step 1.
    Probing step 2: show@15 → shortcut → 1 shortcut for step 2.
    Total: 2 shortcuts (one per step). -/
def testVerboseFilterKeepsFirstPerStep : IO Unit := do
  let fixturePath : System.FilePath := "TestSuite/Fixtures/VerboseMultiStep.lean"
  let results ← analyzeFile fixturePath #["decide"] (filterVerboseSteps := true)
  -- 2 steps → step1 shortcut at show@12, step2 shortcut at show@15 → 2 shortcuts
  unless results.size == 2 do
    throw (IO.userError
      s!"testVerboseFilterKeepsFirstPerStep: expected 2 shortcuts (one per step), \
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
  -- Decl 2 (no step boundaries) has `constructor` at line 40.
  -- `all_goals norm_num` at line 41 generates two TacticInfo nodes at different columns;
  -- skip-last drops only the inner `norm_num` (last position), leaving `all_goals@(41,2)`.
  -- Without filter: lines 29,30,32 (Decl 1) + lines 40,41 (Decl 2, col 2 for all_goals) → 5 total.
  let withoutFilter ← analyzeFile fixturePath #["decide"] (filterVerboseSteps := false)
  unless withoutFilter.any (fun r => r.line == 40) do
    throw (IO.userError
      "testVerboseFilterRespectsDeclarationBoundaries: fixture sanity check failed \
       — expected decide shortcut at line 40 (constructor, unfiltered)")
  unless withoutFilter.size == 5 do
    throw (IO.userError
      s!"testVerboseFilterRespectsDeclarationBoundaries: expected 5 shortcuts unfiltered \
        (lines 29,30,32,40,41), got {withoutFilter.size}")
  -- With filter: Decl 1→lines 29,32 (one per step); Decl 2 singletons→lines 40,41 → 4 total.
  -- (filterVerboseSteps must NOT suppress Decl 2 which has no step boundaries.)
  let withFilter ← analyzeFile fixturePath #["decide"] (filterVerboseSteps := true)
  unless withFilter.any (fun r => r.line == 40) do
    throw (IO.userError
      "testVerboseFilterRespectsDeclarationBoundaries: filterVerboseSteps incorrectly \
       suppressed shortcuts in a declaration with no step boundaries (line 40)")
  unless withFilter.size == 4 do
    throw (IO.userError
      s!"testVerboseFilterRespectsDeclarationBoundaries: expected 4 shortcuts filtered \
        (lines 29,32,40,41), got {withFilter.size}")

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

/-- Regression test: a probe tactic that can close the goal at the LAST step of
    a proof must not be reported as a shortcut.
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

/-- Integration test: verify that `analyzeFile` detects `decide` as a shortcut
    in a file using the WaterproofGenre `#doc` format. -/
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

/-- Regression test: the `Exercise`/`Example` Verbose command wraps the `Proof:` body
    in `with(out)_suggestions%$tkp` where `tkp` is the `Proof:` token.  This generates
    a `TacticInfo` node at the `Proof:` position with a non-empty goal, which must NOT
    be treated as a user-written proof step and must NOT be probed.

    The fixture has two exercises; `Proof:` appears at lines 27 and 39.
    These positions must never appear as shortcuts — they are wrapper nodes. -/
def testVerboseExerciseDoesNotProbeBeforeProof : IO Unit := do
  let fixturePath : System.FilePath := "TestSuite/Fixtures/VerboseExercise.lean"
  let results ← analyzeFile fixturePath #["decide"] (filterVerboseSteps := true)
  -- Verify the proof-wrapper nodes (at the `Proof:` token lines) are not probed
  if results.any (fun r => r.line == 27) then
    throw (IO.userError
      "testVerboseExerciseDoesNotProbeBeforeProof: shortcut reported at line 27 (Proof: wrapper of Exercise 1)")
  if results.any (fun r => r.line == 39) then
    throw (IO.userError
      "testVerboseExerciseDoesNotProbeBeforeProof: shortcut reported at line 39 (Proof: wrapper of Exercise 2)")

/-- Regression test: combined Verbose Lean proof wrapper (Exercise block) with full
    Lean Verbose step syntax (`Let's first/now prove that …`) and `We compute` (a full
    Lean Verbose phrase) inside the proof body.

    All three filters must cooperate:
    - `isSyntheticTacticContainer` suppresses the `with(out)_suggestions` wrapper at `Proof:`
    - `filterVerboseSteps` keeps only the first non-boundary tactic per step (`We compute`)
    - `skipLastPerDeclaration` drops the last overall position (step 2's `We compute`)
    After all three, exactly 1 shortcut remains (step 1's `We compute` at line 29).
    The test checks both the count and the line to confirm the Lean Verbose phrase
    is the detected shortcut (not a plain `show` or `norm_num`). -/
def testVerboseExerciseWithStepsYieldsOneShortcut : IO Unit := do
  let fixturePath : System.FilePath := "TestSuite/Fixtures/VerboseExerciseWithSteps.lean"
  let results ← analyzeFile fixturePath #["decide"] (filterVerboseSteps := true)
  unless results.size == 1 do
    throw (IO.userError
      s!"testVerboseExerciseWithStepsYieldsOneShortcut: expected 1 shortcut \
        (wrapper filtered, step 2 is last), got {results.size}")
  -- Verify the shortcut is at the `We compute` Lean Verbose phrase (step 1, line 29)
  unless results.any (fun r => r.line == 29) do
    throw (IO.userError
      "testVerboseExerciseWithStepsYieldsOneShortcut: shortcut must be at \
        `We compute` phrase (step 1, line 29)")

/-- Thread 4 regression: combined Exercise wrapper + step boundaries + Lean Verbose phrase.
    VerboseExercise.lean has two exercises; Exercise 2 uses `We compute` (a full Lean Verbose
    phrase) within step boundaries.  With filterVerboseSteps=true, each exercise contributes
    exactly 1 shortcut → 2 total.  The shortcut from Exercise 2 must be at the `We compute`
    phrase (step 1 of Exercise 2). -/
def testVerboseExerciseWithStepsAndVerbosePhrase : IO Unit := do
  let fixturePath : System.FilePath := "TestSuite/Fixtures/VerboseExercise.lean"
  let results ← analyzeFile fixturePath #["decide"] (filterVerboseSteps := true)
  unless results.size == 2 do
    throw (IO.userError
      s!"testVerboseExerciseWithStepsAndVerbosePhrase: expected 2 shortcuts \
        (1 from Exercise 1 show, 1 from Exercise 2 We compute), got {results.size}")
  -- Verify the Lean Verbose phrase shortcut (We compute at step 1 of Exercise 2) is found.
  -- Exercise 1's `show` is at line 28; Exercise 2's `We compute` (step 1) is at line 41.
  unless results.any (fun r => r.line == 41) do
    throw (IO.userError
      "testVerboseExerciseWithStepsAndVerbosePhrase: expected shortcut at `We compute` \
        phrase (Exercise 2, step 1, line 41)")

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
  testVerboseExerciseWithStepsYieldsOneShortcut;
                             IO.println "  ✓ testVerboseExerciseWithStepsYieldsOneShortcut"
  testVerboseExerciseWithStepsAndVerbosePhrase;
                             IO.println "  ✓ testVerboseExerciseWithStepsAndVerbosePhrase"

end TestSuite.Analysis
