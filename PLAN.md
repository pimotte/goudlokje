# Rearchitecting Position Tracking in Goudlokje

## TL;DR

We have two competing position paradigms: **shortcuts** use `lineInProof` (relative within proof), while **lint checks** use absolute `line:column`. Both are fragile in different ways. The plan proposes using a **stable, semantic identifier model** for shortcuts (`exercise`, `stepNumber`, `tacticIndexInStep`) scoped to **Verbose proofs only** and **fuzzy matching** for lint. Old `.test.json` files are regenerated via `update --all` — no backward compatibility layer.

**Scope**: Shortcuts and the semantic position model apply only to Verbose proofs (those with `Let's prove that` step boundaries). Non-Verbose proofs are not supported for shortcut detection. **Nested Verbose proofs are not supported** — shortcuts are only recorded for top-level Verbose proofs.

**Display**: All information is shown to the teacher: `[{exercise}: step X, tactic Y] — <tactic text>`.

---

## 1. Current State

### 1.1 Shortcut Position Model

```
ProbeResult:
  exercise    : String   ← "1.1.13"
  lineInProof : Nat      ← relative position within proof (1-based)
  tactic      : String   ← "decide"
```

`lineInProof` is computed in `analyzeInput` (Analysis.lean):

```lean
let proofStartLine ← -- set when first tactic of a declaration-group is seen
let lineInProof := pos.line - proofStartLine + 1
```

### 1.2 Lint Check Position Model

```
LintResult:
  line    : Nat   ← absolute file line (1-based)
  column  : Nat   ← absolute file column (0-based)
```

Stored in `.test.json` as absolute positions.

### 1.3 Matching Semantics

**Shortcuts:** Match on `{exercise, lineInProof, tactic}`. The absolute `line`/`column` fields on `ProbeResult` exist but are **never used for matching** — they are only displayed to the teacher.

**Lint:** Match on `{file, line, column, check}`. Absolute positions.

---

## 2. Problems

### Problem 1: `lineInProof` ≠ actual proof-relative position

`proofStartLine` is set when the **first `TacticInfo` node** encountered for a `parentDecl?` group is seen. This is unreliable because:

**a) `proofStartLine` is per-declaration, not per-proof.** A single declaration (e.g. `#doc` with multiple exercises) can contain multiple proofs. `lineInProof` values from the second proof will be offset by the first proof's length.

Example — two exercises in one `#doc` block:
```
Exercise "1.1"          ← line 9
Proof:
  Since A we conclude B   ← TacticInfo at line 11 → proofStartLine = 11
  norm_num                ← line 12
QED

Exercise "1.2"          ← line 15
Proof:
  Since C we conclude D   ← TacticInfo at line 17
  norm_num                ← line 18
```

At line 17, `decl` may be the same `parentDecl?` as line 11, so `proofStartLine` stays `11`. Thus:
- `1.1` tactics: `lineInProof` = {1, 2} ✓
- `1.2` tactics: `lineInProof` = {6, 7} ✗ — should be {1, 2}

The exercise name distinguishes them, but the `lineInProof` values are meaningless for the second proof. A teacher editing proof `1.2` sees `lineInProof: 6` and has no idea which tactic that is.

**b) Synthetic container nodes can set `proofStartLine` too early.** A proof wrapper `withSuggestions` or `by` block at a non-proof position can generate a `TacticInfo` with non-empty `goalsBefore`. If this appears before the actual first proof tactic, `proofStartLine` gets set to this synthetic position, shifting all `lineInProof` values by `N`.

**c) No cross-run stability guarantee.** If a teacher re-runs `update` after editing a proof (adding/removing tactics), the `proofStartLine` computation can change if the set of `TacticInfo` nodes in that declaration changes (due to elaboration differences between runs). This causes `lineInProof` to shift for tactics that haven't moved.

### Problem 2: Lint checks are brittle on absolute positions

Absolute `line:column` matching fails when:
- Teacher adds a tactic before a lint-violating line → all subsequent `line` values shift by +1
- Teacher reformats the proof (inserting blank lines)
- Teacher copies a proof template and inserts it before existing proofs

Without fuzzy matching, the teacher must manually update every single `line` value in the test file, or run `update --all` which removes stale entries and re-adds them.

### Problem 3: Inconsistent paradigms between shortcuts and lint

Shortcuts ignore absolute position (use `lineInProof`), lint ignores relative position (uses `line:column`). The test file format stores both types differently, increasing cognitive load and maintenance burden.

---

## 3. Design Constraints

1. **User is the teacher** (not the student). The teacher:
   - Writes/maintains exercise files
   - Runs `update` to record expected shortcuts/lints
   - Runs `check` in CI
   - Occasionally re-runs `update` after editing exercises

2. **Stability across edits**: After editing a proof, re-running `update` should match existing expected entries where possible. The teacher should see "same shortcut at same logical position" rather than "completely new shortcut."

3. **Fresh regeneration is acceptable**: If `.test.json` files become stale due to major edits, the teacher runs `update --all` to regenerate them. No backward-compatibility layer for old file formats.

4. **Simplicity**: The teacher shouldn't need to understand the internal position model.

---

## 4. Proposed Model: Semantic Position Identifiers

### Core Idea

Instead of computing `lineInProof` (fragile, declaration-scoped) or using absolute `line:column` (fragile, edit-sensitive), identify **probe positions semantically** using stable structural properties of the proof.

### 4.1 For Shortcuts: Step-Aware Position (Verbose proofs only)

Each tactic position in a Verbose proof is identified by a tuple:

```
ShortcutIdentifier = (exercise : String, stepNumber : Nat, tacticIndexInStep : Nat)
```

Where:
- **`exercise`**: The exercise/theorem name (existing, already used)
- **`stepNumber`**: The 1-based index of the Verbose proof step this tactic belongs to (1 for the first `Let's prove that`, 2 for the second, etc.)
- **`tacticIndexInStep`**: The 1-based index of the tactic within its step

**Scope**: Shortcuts only apply to Verbose proofs (those with `Let's prove that` step boundaries). Non-Verbose proofs are not supported.

#### Why this works

- **Stable across edits**: Step boundaries (`Let's prove that`) are user-written and edited deliberately. Adding/removing tactics within a step shifts `tacticIndexInStep` but not `stepNumber`. Only adding/removing step boundaries changes the matching key.
- **Cross-proof isolation**: Each proof gets its own `stepNumber` starting from 1. No confusion like "is `lineInProof: 7` the 7th line or the 7th tactic?"
- **Meaningful for the teacher**: "Step 1" maps directly to "the first `Let's prove that` block" — something the teacher can reason about.

#### Handling the filter pipeline

The existing `applyVerboseStepFilter` and `skipLastPerDeclaration` already group tactics by step boundaries (`isVerboseStepBoundary`). We just need to assign stable step numbers:

1. Group all tactics by their enclosing **proof** (identified by `Exercise "name"` boundaries or `parentDecl?` + proof wrapper detection)
2. Within each proof, assign `stepNumber` based on `isVerboseStepBoundary` markers
3. Within each step, assign `tacticIndexInStep` by source order

### 4.2 For Lint Checks: Absolute Position (unchanged, with one improvement)

Lint checks stay on absolute `line:column` because:
- Lint violations are **file-level diagnostics**, not proof-level
- The teacher expects to see "raw Lean tactic at line 15" — this is immediately actionable
- Lint check positions are typically sparse (few violations per file)

**Improvement**: Add a **context hint** to the stored lint entry. Store a short snippet of the offending line (first 40 chars) alongside the position. During matching:
1. First try exact `line:column` match (current behavior)
2. If no match, search ±5 lines for a line starting with the same token (e.g. `exact`, `Fix`, `sorry`)
3. If found, update the stored position to the new line number

This makes lint entries somewhat resilient to nearby edits without requiring full re-parsing of the proof structure.

### 4.3 New Storage Format

The `.test.json` file format changes:

**Shortcuts:**
```json
{
  "exercise": "1.1.13",
  "stepNumber": 2,
  "tacticIndexInStep": 1,
  "tactic": "decide"
}
```

**Lint:** unchanged (absolute `line:column` + `message` = full tactic text at that line).

**Full `.test.json` example:**
```json
{
  "shortcuts": [
    {
      "exercise": "1.1.13",
      "stepNumber": 2,
      "tacticIndexInStep": 1,
      "tactic": "decide"
    },
    {
      "exercise": "1.2.7",
      "stepNumber": 1,
      "tacticIndexInStep": 3,
      "tactic": "norm_num"
    }
  ],
  "lint": [
    {
      "check": "B2",
      "line": 42,
      "column": 7,
      "message": "Fix x : Nat"
    }
  ]
}
```

**Regeneration**: If `.test.json` files become stale or need format migration, the teacher runs `update --all` to regenerate them. No backward-compatibility layer for old formats. No version field.

---

## 5. Detailed Design

### 5.1 New Structure Types

```lean
/-- Semantic identifier for a shortcut probe position.
    Identifies a tactic by its logical role in a proof, independent
    of source-line positioning. Uses tacticIndexInStep as primary key. -/
structure ShortcutId where
  exercise        : String  -- e.g. "1.1.13"
  stepNumber      : Nat     -- 1-based step index within the proof
  tacticIndexInStep : Nat   -- 1-based tactic index within its step

/-- A probe result now carries a semantic ID alongside the raw position.
    Verbose proofs only. Non-Verbose proofs produce no shortcut entries.
    -/
structure ProbeResult where
  file            : String
  line            : Nat     -- absolute position (kept for lint; shortcuts use stepNumber/tacticIndexInStep)
  column          : Nat
  exercise        : String
  id              : ShortcutId  -- Verbose proof only; non-Verbose proofs produce no entries
  tactic          : String
```

### 5.2 Computing `stepNumber` and `tacticIndexInStep`

```
For each declaration group:
  1. Sort TacticInfo nodes by source position
  2. Walk through nodes, tracking:
     - currentProof: starts fresh at each Exercise/Example boundary
     - currentStep: 1 initially, increments at each isVerboseStepBoundary
     - currentTacticIndex: 1 initially, increments for each tactic in the step

  3. For each surviving (filtered) tactic:
     - shortcutId = { exercise, stepNumber: currentStep, tacticIndexInStep: currentIndex }
```

Proof boundary detection:
- For Verbose Waterproof: detect `Exercise "name"` / `Example "name"` markers. Track when `findExerciseName` returns a **different** name than the previous exercise — this is a new proof boundary.
- For regular Lean: `parentDecl?` changes. Each new `parentDecl?` starts a fresh proof.
- Key fix: **reset step counters at each proof boundary**, not just at each declaration boundary. This is the fix for the current `proofStartLine` bug.

**Verbose-only**: Only tactics inside Verbose proofs (those with `isVerboseStepBoundary` markers) produce `ProbeResult` entries with semantic IDs. Non-Verbose proofs produce no shortcut entries.

Step boundary detection:
- `isVerboseStepBoundary` identifies step boundaries (existing logic)
- Within a step, tactics are counted in source order
- The first tactic of a step (right after the step boundary, or the first tactic if no boundary precedes it) has `tacticIndexInStep = 1`

### 5.3 Shortcut Matching Logic

```lean
/-- Match a shortcut against expected entries. Match on exercise + stepNumber + tactic
    only. tacticIndexInStep is stored for display but ignored for matching, so
    within-step edits (adding/removing tactics) do not break existing entries. -/
def matchesEntry (r : ProbeResult) (e : ExpectedShortcut) : Bool :=
  e.exercise == r.id.exercise &&
  e.stepNumber == r.id.stepNumber &&
  e.tactic == r.tactic
```

`stepNumber` is anchored to Verbose step boundaries (`Let's prove that`, etc.), which
the teacher touches deliberately. Adding/removing tactics *within* a step changes
`tacticIndexInStep` but not `stepNumber`, so the shortcut still matches. Only adding
or removing a step boundary changes the `stepNumber` and causes a mismatch.

### 5.4 Lint Matching Improvement

```lean
/-- Try to match a lint result against expected entries.
    Strategy: exact position first, then fuzzy search in nearby lines. -/
def classifyLintWithFuzzy
    (found : Array LintResult) (tf : TestFile) : LintClassificationResult :=
  let violations := found.map fun r =>
    if r.check == "B1" then .unexpected r
    else
      -- Try exact match first
      if tf.lint.any (lintMatchesEntry r) then .expected r
      else
        -- Try fuzzy match: same check, same tactic token, ±5 lines
        let fuzzyMatch := findFuzzyLintMatch r tf.lint
        if fuzzyMatch then
          -- Return as expected but note that position should be updated
          -- (handled in update mode)
          .expected r
        else
          .unexpected r
```

### 5.5 README Documentation

Add/update these sections in the project README.md:

**Section: "Expected shortcuts (.test.json)"** — update to explain the new format:
```
{
  "exercise": "1.1.13",
  "stepNumber": 2,
  "tacticIndexInStep": 1,
  "tactic": "decide"
}
```
- `stepNumber`: which step in the proof (1 = first step, 2 = second step, etc.)
- `tacticIndexInStep`: which tactic within that step (1-based)

**Section: "How Goudlokje identifies positions"** — new section:
```
Shortcut positions are identified by exercise name + step number + tactic index,
not by absolute line numbers. This means:
- Adding tactics to other exercises doesn't affect shortcut detection in other
  exercises
- Adding tactics within the same step may shift tactic indices; run `update`
  to refresh the test file

Lint positions are identified by absolute line:column with fuzzy matching:
if an exact position match fails, Goudlokje searches ±5 lines for a matching
tactic token. If found, the violation is still treated as documented and the
position is updated on the next `update` run.
```

### 5.6 Update Mode Changes

When `update` runs:
1. For shortcuts: new-format entries are saved with `stepNumber`/`tacticIndexInStep`
   (`tacticIndexInStep` is not used for matching — it's for display/precision)
2. For shortcuts: entries not matched by `{exercise, stepNumber, tactic}` are stale
   (removed with confirmation in interactive mode)
3. For lint: if a fuzzy match found, update the stored `line`/`column` to the new position (and confirm with teacher)
4. Stale entries: entries that can't be matched even with fuzzy search are flagged for removal

Stale shortcuts occur only when the teacher adds/removes a **step boundary** (not when
they add/remove tactics within a step — `stepNumber` stays the same).

Display format for the teacher (showing all information: step, tactic index, and tactic text):
```
Shortcut [1.1.13: step 2, tactic 1] — `norm_num` closes goal at "rfl"
Accept? [y/N]
```
```
Stale: [1.1.13: step 1, tactic 2] — `trivial` no longer closes goal at step 1, tactic 2
Remove? [y/N]
```
```
Lint [B2] at line 15 — `Fix x : Nat`
Accept? [y/N]
```

### 5.7 Check Mode Changes

- `check` compares found shortcuts against expected entries using `{exercise, stepNumber, tactic}`
- Any mismatch → reported as **unexpected** (shortcut found but not in test file), displayed as:
  ```
  ⚠ example: step 2, tactic 1 — `decide` (unexpected)
  ```
- Any expected entry not matched → reported as **stale** (in test file but no longer triggered), displayed as:
  ```
  ⚠ example: step 1, tactic 2 — `trivial` (stale, in test file but not triggered)
  ```
- Lint check behavior: exact match first, fuzzy fallback ±5 lines matching same check + **full tactic text**
- When a lint fuzzy match is found: counts as expected, and the position is updated
  on the next `update` run
- Output ends with a summary (expected shortcuts are NOT listed individually):
  ```
  ✓ 3 expected
  ⚠ 2 stale
  ⚠ 1 unexpected
  ```

---

## 6. Migration Plan

No backward-compatibility migration needed. No version field in `.test.json`. All files are regenerated
from scratch via `update --all`.

1. Add `ShortcutId` structure and `id` field to `ProbeResult`
2. Add `stepNumber`, `tacticIndexInStep` fields to `ExpectedShortcut`, remove `lineInProof`
3. Update `analyzeInput` to compute `id` (no `lineInProof`)
4. Update `classify` to match on `{exercise, stepNumber, tactic}`
5. Update `TestFile.lean` JSON serialization for new format
6. Implement fuzzy matching for lint entries
7. Run `update --all` on existing projects to regenerate `.test.json` files

---

## 7. Grilled Decisions (resolved with user)

### D1: Stability goal — "survive edits outside the current exercise"

The requirement: if the teacher adds/removes lines in **other** exercises (not the one containing the shortcut), the shortcut should still match. Within the *same* exercise, if the teacher adds/removes tactics, the shortcut may shift — that's acceptable.

This means step-aware positioning is the right granularity. Steps are anchored to Verbose step boundaries (user-written `Let's prove that` etc.), which the teacher touches deliberately. Tactics within a step may shift if the teacher adds tactics, but that's expected and reviewed during `update`.

### D2: Lint — fuzzy matching documented

Fuzzy matching for lint entries: if exact `line:column` match fails, search ±5 lines for a line starting with the same tactic token. This is documented clearly in the README and the `.test.json` file format.

### D3: Fix `proofStartLine` bug now

The current per-declaration `proofStartLine` bug (multiple proofs in one `#doc` block share one offset) is fixed as part of this rearchitect. New semantic IDs naturally avoid this bug.

### D4: Display tactic text to the teacher

All messages shown to the teacher (`update` prompts, `check` output) include the actual tactic text at the relevant position, in addition to the semantic identifier. Example:
```
Shortcut [1.1.13: step 1, tactic 1] — `show 1 + 1 = 2` closes the goal
```
The `.test.json` file stores only the semantic ID (no tactic text).

### D5: Step granularity — match on stepNumber, keep tacticIndexInStep for display

We chose: keep `tacticIndexInStep` in the structure (for display/precision) but match on `{exercise, stepNumber, tactic}` only.

**Rationale**: Most teacher edits are adding/removing tactics *within* a step (rewriting tactic text, inserting intermediate `have`, etc.). These change `tacticIndexInStep` but not `stepNumber`. Matching on `stepNumber` alone means shortcuts survive these routine edits. The `tacticIndexInStep` field is kept in the JSON for display purposes (showing the teacher which tactic in the step a shortcut was at) but plays no role in matching.

**Trade-offs accepted**:
- Two different shortcuts at the same step with the same tactic (e.g., `decide` at step 1, tactic 1 and `decide` at step 1, tactic 3) are treated as the same entry. This is acceptable because if `decide` truly closes the goal at two different positions in the same step, only one needs to be recorded (the teacher can adjust the proof if needed).
- The teacher sees "step 2" in output instead of "step 2, tactic 3". The full index is still available in the `.test.json` file for precision.

### Concrete example: adding a tactic within a step

```
Before:
  step 1, tactic 1: show 1 + 1 = 2
  step 1, tactic 2: norm_num          ← shortcut: decide closes here
  step 1, tactic 3: rfl

After (teacher adds a have):
  step 1, tactic 1: show 1 + 1 = 2
  step 1, tactic 2: have h : ... := by ...  ← new
  step 1, tactic 3: norm_num          ← was tactic 2, now tactic 3
  step 1, tactic 4: rfl
```

With `stepNumber` matching: `stepNumber: 1, tactic: "decide"` matches → **expected** (auto-accepted). The `tacticIndexInStep` in the test file may be stale (shows 2, actual is 3) but this doesn't affect matching. On next `update --all`, the file is refreshed.

### Concrete example: adding/removing a step boundary

```
Before:
  step 1, tactic 1: show 1 + 1 = 2
  step 1, tactic 2: norm_num          ← shortcut: decide closes here

After (teacher splits into two steps):
  step 1, tactic 1: show 1 + 1 = 2
  Let's prove that 0 + 1 = 1
    norm_num                          ← was step 1/tactic 2, now step 2
```

With `stepNumber` matching: the shortcut at `step 1` no longer matches the new `step 2` position → reported as **stale** (in test file) and **unexpected** (found at step 2). Teacher reviews both.

### Q2: Nested proofs — limitation

Waterproof proofs with nested `Let's prove that N works` blocks create sub-proofs that produce `TacticInfo` nodes at the same position as the outer tactic. The opaque subtree pruning currently suppresses these, so nested proofs are **not supported** — shortcuts are only recorded for top-level Verbose proofs.

**Limitation**: If a teacher uses nested `Let's prove that` blocks, shortcuts inside the nested blocks will not be detected. This is acceptable because nested Verbose proofs are rare in typical exercises. If needed in the future, the filter pipeline can be extended to track nested step boundaries as a separate dimension.

### Q3: Non-Verbose proofs

Non-Verbose proofs are silently ignored by `update` — they produce no shortcut entries and are not recorded in `.test.json`. What happens to stale non-Verbose entries in old `.test.json` files is irrelevant; `update --all` will overwrite them. This keeps the codebase simple: no migration logic, no cleanup passes.

### Q4: Lint and semantic positions

Lint violations are **file-level diagnostics**, not proof-level. The semantic position model does not apply to lint checks. Lint retains its absolute `line:column` positioning with fuzzy matching (±5 lines) as a resilience improvement. Fuzzy matching compares the **full tactic text** (not just the name/keyword). The `message` field contains the **full tactic text** at that line.

### Q5: Display to the teacher

The display to the teacher shows **all available information**: `exercise`, `stepNumber`, `tacticIndexInStep`, and the tactic text at that line. Tactic text is **truncated at 60 characters** in prompts. This gives the teacher full context to make informed decisions.

### Q6: Update with no Verbose proofs

If `update` runs on a `.lean` file with no Verbose proofs, it skips silently and does not generate a `.test.json` file. Non-Verbose proofs produce no shortcut entries.

### Q7: Lint `message` field naming

The `message` field name for lint entries uses whatever name already exists in the codebase (e.g., `text`, `note`, etc.). This avoids adding unnecessary field renaming.

### Q8: `.test.json` versioning

No version field in `.test.json`. The file is simply overwritten on each `update --all`. This keeps the format minimal.

Example prompts:
```
Shortcut [example: step 2, tactic 1] — `norm_num` closes goal at "rfl"
Accept? [y/N]

Stale: [example: step 1, tactic 2] — `trivial` no longer closes goal at step 1, tactic 2
Remove? [y/N]

Lint [B2] at line 15 — `Fix x : Nat`
Accept? [y/N]
```

`check` output ends with a summary:
```
✓ 3 expected
⚠ 2 stale
⚠ 1 unexpected
```

The `.test.json` file stores the semantic ID (`stepNumber`, `tacticIndexInStep`) but **not** the tactic text. The tactic text is shown in prompts by looking it up from the source file at analysis time.

---

## 8. Risks and Mitigations

| Risk | Mitigation |
|------|-----------|
| Stale entries accumulate | `update --all` regenerates all `.test.json` files |
| Step numbering changes after re-runs | Deterministic source-order-based numbering |
| Fuzzy lint matching produces false positives | Keep fuzzy as fallback only; require exact match first |
| Nested proofs not supported | Documented as a limitation; acceptable for typical exercises |

---

## 9. Implementation Order

1. **`TestFile.lean`**: Update `ExpectedShortcut` — add `stepNumber`, `tacticIndexInStep`, remove `lineInProof`. Update JSON serialization.
2. **`Analysis.lean`**: Add `ShortcutId` computation in `analyzeInput` — compute `id` from step-aware walk. Remove `lineInProof` computation.
3. **`Shortcuts.lean`**: Update `matchesEntry` to use `{exercise, stepNumber, tactic}`
4. **`Lint.lean`**: Add fuzzy matching for lint entries
5. **`Update.lean`**: Update prompts to show new semantic identifiers
6. **`Check.lean`**: Uses `classify` — no code changes needed
7. **Test suite**: Update fixture tests, add tests for new position model

---

## 10. Summary

The core insight: **shortcut positions should be identified by their logical role in the proof, not by their source-line position**. Matching uses `{exercise, stepNumber, tactic}` — `stepNumber` is anchored to Verbose step boundaries, so shortcuts survive within-step edits. `tacticIndexInStep` is stored but not used for matching (it tracks the actual tactic position within the step for display/precision).

Display to the teacher shows all information: `[{exercise}: step X, tactic Y] — <tactic text>` — giving full context for informed decisions. Lint checks stay on absolute positions with fuzzy matching resilience (±5 lines, full tactic text comparison); no semantic positioning for lint.

**Scope**: The semantic position model applies only to Verbose proofs (those with `Let's prove that` step boundaries). Non-Verbose proofs produce no shortcut entries. **Nested Verbose proofs are not supported** — shortcuts are only recorded for top-level Verbose proofs.

`.test.json` files are regenerated via `update --all` — no backward compatibility layer, no version field.

`check` output shows expected count but NOT individual expected entries. Non-Verbose proofs are silently skipped (no `.test.json` generated). Lint `message` field uses existing codebase naming.
