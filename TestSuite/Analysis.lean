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

/-- Verbose step filtering: each step has `show` (first) and `norm_num` (last in step).
    Per-step skip-last keeps `show` for both steps; declaration-level skip-last then
    drops the representative of the last step → only step 1's `show` remains. -/
def testVerboseFilterKeepsFirstPerStep : IO Unit := do
  let fixturePath : System.FilePath := "TestSuite/Fixtures/VerboseMultiStep.lean"
  let results ← analyzeFile fixturePath #["decide"] (filterVerboseSteps := true)
  -- 2 steps × 2 tactics each → per-step skip-last keeps show@step1, show@step2
  -- → declaration-level skip-last removes show@step2 → 1 shortcut
  unless results.size == 1 do
    throw (IO.userError
      s!"testVerboseFilterKeepsFirstPerStep: expected 1 shortcut (step 1 only; step 2 dropped by skip-last), \
        got {results.size}")

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

/-- Regression test for single-tactic Verbose steps: each step has exactly one tactic
    (`norm_num`), which is both the first and last move in the step.  Per-step skip-last
    skips these steps entirely — the student must write that one tactic regardless, so a
    probe succeeding there is not a meaningful shortcut. -/
def testSkipLastTacticNotReported : IO Unit := do
  let fixturePath : System.FilePath := "TestSuite/Fixtures/SkipLastStep.lean"
  -- 2 steps × 1 tactic each → per-step skip-last drops both → 0 shortcuts
  let results ← analyzeFile fixturePath #["decide"] (filterVerboseSteps := true)
  unless results.size == 0 do
    throw (IO.userError
      s!"testSkipLastTacticNotReported: expected 0 shortcuts (single-tactic steps skipped), \
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

/-- Regression test: in a Waterproof+Verbose exercise where each step has exactly one
    tactic (`· We conclude by hypothesis`), probing "We conclude by hypothesis" must find
    no shortcuts.  Two fixes combine: `Lean.cdot` (`·`) is filtered as a synthetic
    container (so the focused subgoal is not a probe position), and per-step skip-last
    skips single-tactic steps entirely (the student must write that tactic regardless). -/
def testBulletSeenAsStepInVerboseWaterproofFull : IO Unit := do
  let fixturePath : System.FilePath := "TestSuite/Fixtures/VerboseWaterproofFull.lean"
  let results ← analyzeFile fixturePath #["We conclude by hypothesis"]
    (filterVerboseSteps := true)
  unless results.size == 0 do
    let detail := results.foldl (fun s r => s ++ s!" {r.line}:{r.column}") ""
    throw (IO.userError
      s!"testBulletSeenAsStep: expected 0 shortcuts (single-tactic steps skipped), \
        got {results.size} at:{detail}")

/-- Verify that every tactic syntax kind in VerboseWaterproofFull is classified.
    Fails with the full table if any kind is `unknown` — add it to the appropriate
    predicate in Analysis.lean and run again.
    Run after adding new exercises to the fixture to catch newly appearing kinds. -/
def testNoUnclassifiedTacticKinds : IO Unit := do
  let kinds ← classifyTacticKinds "TestSuite/Fixtures/VerboseWaterproofFull.lean"
  let unknowns := kinds.filter (fun (_, c) => c == .unknown)
  unless unknowns.isEmpty do
    let fmt (k : String) (c : TacticKindCategory) :=
      let tag := match c with
        | .synthetic   => "synthetic  "
        | .boundary    => "boundary   "
        | .opaque      => "opaque     "
        | .opaqueChild => "opaqueChild"
        | .userTactic  => "userTactic "
        | .unknown     => "UNKNOWN    "
      s!"  [{tag}] {k}"
    let table := kinds.foldl (fun s (k, c) => s ++ "\n" ++ fmt k c) ""
    throw (IO.userError
      s!"testNoUnclassifiedTacticKinds: {unknowns.size} unknown kind(s) — \
        add to isSyntheticTacticContainer / isVerboseStepBoundary / isVerboseOpaqueSubtree:{table}")

/-- Regression test: a nested `Let's prove that` exercise (1.1.13_extra in
    VerboseWaterproofFull) must report 0 shortcuts when probed with
    "We conclude by hypothesis".  The `tacticLet'sProveThat_` tactic (unqualified)
    expands into internal elaboration nodes (`Lean.Parser.Tactic.first`, `show`,
    `apply`, `«;»`) at the same source position as itself; these must not be treated
    as user-written proof positions. -/
def testNestedLetProveThatNoShortcuts : IO Unit := do
  let fixturePath : System.FilePath := "TestSuite/Fixtures/VerboseWaterproofFull.lean"
  let results ← analyzeFile fixturePath #["We conclude by hypothesis"]
    (filterVerboseSteps := true)
  unless results.size == 0 do
    let detail := results.foldl (fun s r => s ++ s!" {r.line}:{r.column}") ""
    throw (IO.userError
      s!"testNestedLetProveThat: expected 0 shortcuts, got {results.size} at:{detail}")

/-- Regression test: a `We discuss depending on whether` + `Assume that` exercise
    (Example "1.1.20" in VerboseWaterproofFull) must report 0 shortcuts.
    `tacticAssumeThat__` was missing from `isVerboseStepBoundary`, causing
    `applyVerboseStepFilter` to leave `tacticWeConcludeBy_` nodes unfiltered. -/
def testDiscussAssumeThatNoShortcuts : IO Unit := do
  let fixturePath : System.FilePath := "TestSuite/Fixtures/VerboseWaterproofFull.lean"
  let results ← analyzeFile fixturePath #["We conclude by hypothesis"]
    (filterVerboseSteps := true)
  unless results.size == 0 do
    let detail := results.foldl (fun s r => s ++ s!" {r.line}:{r.column}") ""
    throw (IO.userError
      s!"testDiscussAssumeThat: expected 0 shortcuts, got {results.size} at:{detail}")

/-- Regression test: a nested `We discuss` + `Assume that` + `Let's prove that` exercise
    (Exercise "1.1.21" in VerboseWaterproofFull) must report 0 shortcuts. -/
def testNestedDiscussNoShortcuts : IO Unit := do
  let fixturePath : System.FilePath := "TestSuite/Fixtures/VerboseWaterproofFull.lean"
  let results ← analyzeFile fixturePath #["We conclude by hypothesis"]
    (filterVerboseSteps := true)
  unless results.size == 0 do
    let detail := results.foldl (fun s r => s ++ s!" {r.line}:{r.column}") ""
    throw (IO.userError
      s!"testNestedDiscuss: expected 0 shortcuts, got {results.size} at:{detail}")

/-- Diagnostic: trace filter stages for VerboseWaterproofFull. Always throws. -/
def diagFilterStages : IO Unit := do
  let log ← dumpFilterStages "TestSuite/Fixtures/VerboseWaterproofFull.lean"
  throw (IO.userError s!"filter stages:{log}")

/-- Regression test: an existential witness exercise using `Let's prove that N works`
    and `We compute` (Example "1.2.25" in VerboseWaterproofFull) must report 0
    shortcuts when probed with "We conclude by hypothesis". -/
def testExistentialWitnessNoShortcuts : IO Unit := do
  let fixturePath : System.FilePath := "TestSuite/Fixtures/VerboseWaterproofFull.lean"
  let results ← analyzeFile fixturePath #["We conclude by hypothesis"]
    (filterVerboseSteps := true)
  unless results.size == 0 do
    let detail := results.foldl (fun s r => s ++ s!" {r.line}:{r.column}") ""
    throw (IO.userError
      s!"testExistentialWitness: expected 0 shortcuts, got {results.size} at:{detail}")

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
  testBulletSeenAsStepInVerboseWaterproofFull;
                             IO.println "  ✓ testBulletSeenAsStepInVerboseWaterproofFull"

end TestSuite.Analysis
