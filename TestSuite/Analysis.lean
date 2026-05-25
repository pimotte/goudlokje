import Goudlokje.Analysis

namespace TestSuite.Analysis

open Goudlokje

/-- Integration test: verify that `analyzeFile` detects `decide` as a shortcut
    in a Verbose Lean proof.  Issue #13: shortcuts are only reported for Verbose proofs. -/
def testDetectsDecideShortcut : IO Unit := do
  -- Path is relative to the project root (where Lake runs the executable)
  let fixturePath : System.FilePath := "TestSuite/Fixtures/VerboseMultiStep.lean"
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
  let fixturePath : System.FilePath := "TestSuite/Fixtures/VerboseMultiStep.lean"
  let results ← analyzeFile fixturePath #["decide"]
  unless results.size ≥ 1 do
    throw (IO.userError
      s!"testVerbose: expected ≥1 probe result, got {results.size}")
  unless results.any (fun r => r.tactic == "decide") do
    throw (IO.userError
      "testVerbose: expected tactic 'decide' in results")

/-- Integration test: verify that `analyzeFile` does NOT detect shortcuts in a
    Waterproof `#doc` file with non-Verbose proofs.
    Issue #13: shortcut detection is restricted to Verbose Lean proofs only. -/
def testDetectsDecideShortcutInWaterproofFile : IO Unit := do
  let fixturePath : System.FilePath := "TestSuite/Fixtures/Waterproof.lean"
  let results ← analyzeFile fixturePath #["decide"]
  unless results.isEmpty do
    let detail := results.foldl (fun s r => s ++ s!" {r.line}:{r.column}") ""
    throw (IO.userError
      s!"testWaterproof: expected 0 shortcuts in non-Verbose Waterproof file, got {results.size} at:{detail}")

/-- Integration test: verify that `analyzeFile` detects `decide` as a shortcut
    in a file using both WaterproofGenre `#doc` blocks and Lean Verbose tactics
    with `:::input` areas.
    This combination is the typical usage in external Waterproof exercise projects. -/
def testDetectsDecideShortcutInVerboseWaterproofFile : IO Unit := do
  let fixturePath : System.FilePath := "TestSuite/Fixtures/VerboseWaterproofInputArea.lean"
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
  let fixturePath : System.FilePath := "TestSuite/Fixtures/VerboseMultiStep.lean"
  let results ← analyzeFile fixturePath #["decide"]
  for i in List.range results.size do
    for j in List.range results.size do
      if i < j then
        let ri := results[i]!
        let rj := results[j]!
        if ri == rj then
          throw (IO.userError
            s!"testNoDuplicateResults: duplicate [{ri.exercise}: step {ri.id.stepNumber}, tactic {ri.id.tacticIndexInStep}] — `{ri.tactic}`")

/-- Verbose step filtering: `decide` is a shortcut at both the `show` (noop) and
    `norm_num` positions within each step body. The filter keeps only the first
    tactic per step, and skip-last drops the last step's representative → 1 shortcut.
    This verifies the filtered result has the expected count. -/
def testVerboseFilterReducesResults : IO Unit := do
  let fixturePath : System.FilePath := "TestSuite/Fixtures/VerboseMultiStep.lean"
  let results ← analyzeFile fixturePath #["decide"]
  -- 2 steps × 2 tactics each → per-step skip-last keeps show@step1, show@step2
  -- → declaration-level skip-last removes show@step2 → 1 shortcut
  unless results.size == 1 do
    throw (IO.userError
      s!"testVerboseFilter: expected 1 shortcut (filter always on), got {results.size}")

/-- Verbose step filtering: each step has `show` (first) and `norm_num` (last in step).
    Per-step skip-last keeps `show` for both steps; declaration-level skip-last then
    drops the representative of the last step → only step 1's `show` remains.
    Filter is always-on. -/
def testVerboseFilterKeepsFirstPerStep : IO Unit := do
  let fixturePath : System.FilePath := "TestSuite/Fixtures/VerboseMultiStep.lean"
  let results ← analyzeFile fixturePath #["decide"]
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
  let _ ← analyzeFile "TestSuite/Fixtures/VerboseMultiStep.lean" #["decide"]
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
  let results ← analyzeFile "TestSuite/Fixtures/VerboseMultiStep.lean" #["skip"]
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
    A Verbose declaration WITHOUT step boundaries must keep all its tactics even when
    a preceding declaration in the same file DOES have step boundaries.
    Without this, the filter's state leaks across declarations and suppresses
    shortcuts in Verbose exercises without step boundaries. -/
def testVerboseFilterRespectsDeclarationBoundaries : IO Unit := do
  let fixturePath : System.FilePath := "TestSuite/Fixtures/VerboseMultiDecl.lean"
  let results ← analyzeFile fixturePath #["decide"]
  -- Decl 2 is a Verbose Exercise without step boundaries.
  -- It must contribute at least 1 shortcut even though Decl 1 has step boundaries.
  unless results.size ≥ 1 do
    throw (IO.userError
      "testVerboseFilterRespectsDeclarationBoundaries: filter incorrectly \
       suppressed all shortcuts (including Decl 2 which has no step boundaries)")

/-- The number of successful onProbe callbacks equals the number of (deduplicated)
    probe results returned by analyzeFile. -/
def testOnProbeSuccessCountMatchesResults : IO Unit := do
  let successCount ← IO.mkRef (0 : Nat)
  let callback : Nat → Nat → String → Bool → IO Unit := fun _ _ _ success =>
    if success then successCount.modify (· + 1) else pure ()
  -- Use a single-tactic probe so that each (pos, tactic) is hit at most once per goal.
  -- Deduplication means results.size ≤ successCount (multiple goals at a pos count once).
  let results ← analyzeFile "TestSuite/Fixtures/VerboseMultiStep.lean" #["decide"]
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
  let results ← analyzeFile fixturePath #["decide"]
  unless results.size == 0 do
    throw (IO.userError
      s!"testSkipLastTacticNotReported: expected 0 shortcuts (single-tactic steps skipped), \
        got {results.size}")

/-- Regression test: the `Exercise`/`Example` Verbose command wraps the `Proof:` body
    in `with(out)_suggestions%$tkp` where `tkp` is the `Proof:` token.  This generates
    a `TacticInfo` node at the `Proof:` position with a non-empty goal, which must NOT
    be treated as a user-written proof step and must NOT be probed.

    The fixture uses an `Exercise` with a 2-tactic proof and no step boundaries.
    The proof wrapper (`with(out)_suggestions%$tkp`) is filtered as a synthetic container.
    After applying skip-last, exactly 1 shortcut remains (the `show` step).
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

  unless results.size == 0 do
    let detail := results.foldl (fun s r => s ++ s!" {r.line}:{r.column}") ""
    throw (IO.userError
      s!"testDiscussAssumeThat: expected 0 shortcuts, got {results.size} at:{detail}")

/-- Regression test: a nested `We discuss` + `Assume that` + `Let's prove that` exercise
    (Exercise "1.1.21" in VerboseWaterproofFull) must report 0 shortcuts. -/
def testNestedDiscussNoShortcuts : IO Unit := do
  let fixturePath : System.FilePath := "TestSuite/Fixtures/VerboseWaterproofFull.lean"
  let results ← analyzeFile fixturePath #["We conclude by hypothesis"]

  unless results.size == 0 do
    let detail := results.foldl (fun s r => s ++ s!" {r.line}:{r.column}") ""
    throw (IO.userError
      s!"testNestedDiscuss: expected 0 shortcuts, got {results.size} at:{detail}")

/-- Integration test: verify that shortcuts inside the Waterproof :::input block
    are detected while those outside the input area are not. -/
def testInputAreaScoping : IO Unit := do
  let fixturePath : System.FilePath :=
    "TestSuite/Fixtures/VerboseWaterproofInputArea.lean"
  let results ← analyzeFile fixturePath #["decide"]
  unless results.size == 1 do
    throw (IO.userError
      s!"testInputAreaScoping: expected 1 shortcut (inside input area only), \
        got {results.size}")
  let r := results[0]!
  unless r.exercise == "inside-area" do
    throw (IO.userError
      s!"testInputAreaScoping: expected exercise \"inside-area\", got \"{r.exercise}\"")

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

  unless results.size == 0 do
    let detail := results.foldl (fun s r => s ++ s!" {r.line}:{r.column}") ""
    throw (IO.userError
      s!"testExistentialWitness: expected 0 shortcuts, got {results.size} at:{detail}")

/-- Regression test: `Assume for contradiction that …` inside a focused proof bullet
    (the `·` syntax) must NOT produce a false-positive shortcut for "We conclude by
    hypothesis".  The `Assume for contradiction` is a `Verbose.NameLess.tacticAssumeThat__`
    step boundary, and the `·` bullet is filtered as a synthetic container.  Together
    they must produce 0 shortcuts.

    This is a minimal reproduction of the bug reported in `sheet1_subset.lean`
    (exercise 2.1.10): without the fix, the step filter does not correctly exclude
    `Assume for contradiction` at a bullet boundary position, producing a false
    positive shortcut probe. -/
def testAssumeThatInFocusedBulletNoShortcuts : IO Unit := do
  let fixturePath : System.FilePath :=
    "TestSuite/Fixtures/VerboseWaterproofAssumeThatInBullet.lean"
  let results ← analyzeFile fixturePath #["We conclude by hypothesis"]

  unless results.size == 0 do
    let detail := results.foldl (fun s r => s ++ s!" {r.line}:{r.column}") ""
    throw (IO.userError
      s!"testAssumeThatInFocusedBullet: expected 0 shortcuts (Assume for contradiction \
        in focused bullet must not produce a shortcut probe), got {results.size} at:{detail}")

/-- Integration test: a two-step `Since…we get` + `Since…we conclude` exercise
    inside a Waterproof multilean input block has exactly 1 probe point with
    exercise name "1.1.13".
    `skipLastPerDeclaration` drops the final `Since p ∧ q we conclude that q`,
    leaving only the first position where `Since (p ∧ q) ∧ r we conclude that q`
    closes the goal directly — a genuine shortcut. -/
def testSinceGetExerciseHasOneProbePoint : IO Unit := do
  let fixturePath : System.FilePath := "TestSuite/Fixtures/VerboseWaterproofSince.lean"
  let results ← analyzeFile fixturePath #["Since (p ∧ q) ∧ r we conclude that q"]
  unless results.size == 1 do
    let detail := results.foldl (fun s r => s ++ s!" {r.line}:{r.column}") ""
    throw (IO.userError
      s!"testSinceGetExercise: expected exactly 1 probe point (last Since…conclude skipped), \
        got {results.size} at:{detail}")
  let r := results[0]!
  unless r.exercise == "1.1.13" do
    throw (IO.userError
      s!"testSinceGetExercise: expected exercise name \"1.1.13\", got \"{r.exercise}\"")

/-- A file with no :::input markers produces no shortcuts, even when it contains
    Verbose proofs with detectable shortcuts.
    Without student input areas, there is nothing to check. -/
def testNoInputAreasNoShortcuts : IO Unit := do
  let fixturePath : System.FilePath := "TestSuite/Fixtures/VerboseWaterproof.lean"
  let results ← analyzeFile fixturePath #["decide"]
  unless results.isEmpty do
    let detail := results.foldl (fun s r => s ++ s!" {r.line}:{r.column}") ""
    throw (IO.userError
      s!"testNoInputAreasNoShortcuts: expected 0 results for file with no :::input areas, \
        got {results.size} at:{detail}")

/-- Shortcuts must NOT be detected in non-Verbose Lean proofs.
    Issue #13: shortcut detection is restricted to Verbose Lean proofs only. -/
def testShortcutsNotDetectedInNonVerboseFile : IO Unit := do
  let fixturePath : System.FilePath := "TestSuite/Fixtures/Simple.lean"
  let results ← analyzeFile fixturePath #["decide"]
  unless results.isEmpty do
    let detail := results.foldl (fun s r => s ++ s!" {r.line}:{r.column}") ""
    throw (IO.userError
      s!"testShortcutsNotDetectedInNonVerboseFile: expected 0 shortcuts in non-Verbose file, \
        got {results.size} at:{detail}")

/-- Regression test for the internal elaboration artifact bug (sheet1_subset.lean #2).
    Before the fix: `collectTacticInfos` probed at internal elaboration artifact positions
    (e.g. Lean.Parser.Tactic.applyRfl, skip, simp, first, tacticTry_) that share the same
    source position as user-facing Verbose tactics. These internal nodes have `goalsBefore`
    and `isSyntheticTacticContainer` doesn't filter them, so they were incorrectly collected
    as probe positions. This produced false-positive shortcuts like
    "unexpected shortcut — tactic `We conclude by hypothesis` closes the goal" even though
    inserting `We conclude by hypothesis` at those positions gives "This does not conclude".

    The fix adds `isUserFacingVerboseTactic` to `collectTacticInfos`, so only user-facing
    Verbose tactics (Let's first/now/that prove, We conclude by, Since we get/conclude, etc.)
    are collected, and internal elaboration artifacts (Lean.Parser.Tactic.*) are filtered out.

    This test uses the `Since...we get that` + `Since...we conclude that` exercise which
    is NOT opaque and NOT a step boundary. Without the fix, the `Since...we get that` step
    could produce internal elaboration artifact positions that would be incorrectly probed.
    With the fix, only the user-facing `Since...we conclude that` position is collected. -/
def testNoInternalElaborationArtifactShortcuts : IO Unit := do
  let fixturePath : System.FilePath :=
    "TestSuite/Fixtures/VerboseSinceWeConclude.lean"
  -- Probe with "We conclude by hypothesis" — should find no shortcuts at internal
  -- elaboration artifact positions.
  let results ← analyzeFile fixturePath #["We conclude by hypothesis"]

  unless results.isEmpty do
    let detail := results.foldl (fun s r => s ++ s!" {r.line}:{r.column}") ""
    throw (IO.userError
      s!"testNoInternalElaborationArtifactShortcuts: expected 0 shortcuts \
        (internal elaboration artifacts must not be probed), \
        got {results.size} at:{detail}")

/-- Test #2: Non-Verbose proof produces no shortcut entries.
    A plain Lean proof without Verbose step boundaries should not produce any
    ProbeResult entries when probed. -/
def testNonVerboseNoShortcuts : IO Unit := do
  let fixturePath : System.FilePath := "TestSuite/Fixtures/PlainProof.lean"
  let results ← analyzeFile fixturePath #["decide"]
  unless results.isEmpty do
    let detail := results.foldl (fun s r => s ++ s!" {r.line}:{r.column} {r.exercise}") ""
    throw (IO.userError
      s!"testNonVerboseNoShortcuts: expected 0 shortcuts in non-Verbose proof, \
        got {results.size} at:{detail}")

/-- Test #3: Multiple exercises in one file — each gets its own stepNumber.
    Both exercises should have stepNumber 1 (scoped per exercise, not per declaration). -/
def testMultiExerciseInFile : IO Unit := do
  let fixturePath : System.FilePath := "TestSuite/Fixtures/MultiExercise.lean"
  let results ← analyzeFile fixturePath #["decide"]
  unless results.size ≥ 1 do
    throw (IO.userError
      s!"testMultiExerciseInFile: expected ≥1 probe result, got {results.size}")
  -- Verify each exercise gets its own stepNumber starting from 1
  let exNames := results.map (·.exercise)
  unless exNames.any (· == "first") do
    throw (IO.userError
      "testMultiExerciseInFile: expected exercise 'first' in results")
  unless exNames.any (· == "second") do
    throw (IO.userError
      "testMultiExerciseInFile: expected exercise 'second' in results")
  -- Both exercises should have stepNumber 1 (scoped per exercise)
  let firstResults := results.filter (·.exercise == "first")
  let secondResults := results.filter (·.exercise == "second")
  for r in firstResults do
    unless r.id.stepNumber == 1 do
      throw (IO.userError
        s!"testMultiExerciseInFile: 'first' stepNumber should be 1, got {r.id.stepNumber}")
  for r in secondResults do
    unless r.id.stepNumber == 1 do
      throw (IO.userError
        s!"testMultiExerciseInFile: 'second' stepNumber should be 1, got {r.id.stepNumber}")

/-- Test #13: Mixed Verbose and non-Verbose proofs in same file.
    Only the Verbose proof should produce shortcuts. -/
def testMixedVerboseAndNonVerbose : IO Unit := do
  let fixturePath : System.FilePath :=
    "TestSuite/Fixtures/MixedVerbosePlain.lean"
  let results ← analyzeFile fixturePath #["decide"]
  unless results.size ≥ 1 do
    throw (IO.userError
      s!"testMixedVerboseAndNonVerbose: expected ≥1 shortcut from verboseEx, got {results.size}")
  -- All results should be from 'verboseEx'
  for r in results do
    unless r.exercise == "verboseEx" do
      throw (IO.userError
        s!"testMixedVerboseAndNonVerbose: expected exercise 'verboseEx', got '{r.exercise}'")

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
  testAssumeThatInFocusedBulletNoShortcuts;
                             IO.println "  ✓ testAssumeThatInFocusedBulletNoShortcuts"
  testSinceGetExerciseHasOneProbePoint;
                             IO.println "  ✓ testSinceGetExerciseHasOneProbePoint"
  testBulletSeenAsStepInVerboseWaterproofFull;
                             IO.println "  ✓ testBulletSeenAsStepInVerboseWaterproofFull"
  testInputAreaScoping;
                             IO.println "  ✓ testInputAreaScoping"
  testNoInputAreasNoShortcuts;
                             IO.println "  ✓ testNoInputAreasNoShortcuts"
  testShortcutsNotDetectedInNonVerboseFile;
                             IO.println "  ✓ testShortcutsNotDetectedInNonVerboseFile"
  testNoUnclassifiedTacticKinds;
                             IO.println "  ✓ testNoUnclassifiedTacticKinds"
  testNoInternalElaborationArtifactShortcuts;
                             IO.println "  ✓ testNoInternalElaborationArtifactShortcuts"
  testNonVerboseNoShortcuts;
                             IO.println "  ✓ testNonVerboseNoShortcuts"
  testMultiExerciseInFile;
                             IO.println "  ✓ testMultiExerciseInFile"
  testMixedVerboseAndNonVerbose;
                             IO.println "  ✓ testMixedVerboseAndNonVerbose"

end TestSuite.Analysis
