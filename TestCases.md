# Functional Test Cases — Semantic Position Model

## Overview

This document lists functional test cases for the semantic position model rearchitecture.
Each test specifies: **input**, **expected behavior**, and **`.test.json` output**.

**Prerequisites**: All tests assume `update --all` and `check` modes. Fixture Lean files
live in `TestSuite/Fixtures/`.

---

## 1. Basic Verbose Proof — Shortcut Recording

### Input
A simple Verbose proof with 2 steps and 2 tactics per step.

```lean
-- TestSuite/Fixtures/BasicVerbose.lean
example : 1 + 1 = 2 ∧ 2 + 2 = 4 := by
  constructor
  · trivial
  Let's prove that 2 + 2 = 4
    norm_num
    rfl
```

### Expected behavior
`update` records 2 shortcuts:
- `example` step 1, tacticIndexInStep 2: `trivial`
- `example` step 2, tacticIndexInStep 1: `norm_num`

### `.test.json`
```json
{
  "shortcuts": [
    {
      "exercise": "example",
      "stepNumber": 1,
      "tacticIndexInStep": 2,
      "tactic": "trivial"
    },
    {
      "exercise": "example",
      "stepNumber": 2,
      "tacticIndexInStep": 1,
      "tactic": "norm_num"
    }
  ],
  "lint": []
}
```

### Check
`check` runs and reports: **all shortcuts match** (both are expected).

---

## 2. Non-Verbose Proof — No Shortcuts Produced

### Input
A plain Lean proof with no Verbose step boundaries.

```lean
-- TestSuite/Fixtures/PlainProof.lean
example : 1 + 1 = 2 := by
  trivial
```

### Expected behavior
`update` produces **zero** shortcut entries for this proof. The `.test.json` has no
entries for `example`.

### `.test.json`
```json
{
  "shortcuts": [],
  "lint": []
}
```

---

## 3. Multiple Exercises in One File

### Input
Two separate exercises, each with its own Verbose proof.

```lean
-- TestSuite/Fixtures/MultiExercise.lean
theorem first : 1 + 1 = 2 ∧ 2 + 2 = 4 := by
  constructor
  · trivial
  Let's prove that 2 + 2 = 4
    norm_num

theorem second : 3 + 3 = 6 := by
  rw [Nat.add_comm 3 3]
  Let's prove that 3 + 3 = 6
    decide
```

### Expected behavior
`update` records 4 shortcuts:
- `first` step 1, tactic 2: `trivial`
- `first` step 2, tactic 1: `norm_num`
- `second` step 1, tactic 1: `rw [Nat.add_comm 3 3]`
- `second` step 2, tactic 1: `decide`

### `.test.json`
```json
{
  "shortcuts": [
    { "exercise": "first", "stepNumber": 1, "tacticIndexInStep": 2, "tactic": "trivial" },
    { "exercise": "first", "stepNumber": 2, "tacticIndexInStep": 1, "tactic": "norm_num" },
    { "exercise": "second", "stepNumber": 1, "tacticIndexInStep": 1, "tactic": "rw [Nat.add_comm 3 3]" },
    { "exercise": "second", "stepNumber": 2, "tacticIndexInStep": 1, "tactic": "decide" }
  ],
  "lint": []
}
```

### Check
`check` reports all 4 shortcuts match.

---

## 4. Within-Step Tactic Insertion — Shortcut Survives

### Input
Teacher adds a tactic **inside** an existing step.

**Before** (already recorded in `.test.json`):
```lean
example : 1 + 1 = 2 ∧ 2 + 2 = 4 := by
  constructor
  · trivial
  Let's prove that 2 + 2 = 4
    norm_num    ← shortcut: decide closes here
    rfl
```

**After** (teacher edits):
```lean
example : 1 + 1 = 2 ∧ 2 + 2 = 4 := by
  constructor
  · trivial
  Let's prove that 2 + 2 = 4
    have h : 2 + 2 = 4 := by decide  ← new
    norm_num                         ← was tactic 1, now tactic 2
    rfl
```

### Expected behavior
- `check` mode: shortcut matches because `{exercise: "example", stepNumber: 2, tactic: "norm_num"}`
  matches even though `tacticIndexInStep` changed from 1 to 2.
- `update` mode: no stale warning. The entry is accepted as-is.
- On next `update --all`, the `.test.json` is refreshed with `tacticIndexInStep: 2`.

### `.test.json` after refresh
```json
{
  "shortcuts": [
    { "exercise": "example", "stepNumber": 1, "tacticIndexInStep": 2, "tactic": "trivial" },
    { "exercise": "example", "stepNumber": 2, "tacticIndexInStep": 2, "tactic": "norm_num" }
  ],
  "lint": []
}
```

---

## 5. Step Boundary Removal — Shortcut Goes Stale

### Input
Teacher removes a `Let's prove that` step boundary, merging two steps into one.

**Before**:
```lean
example : 1 + 1 = 2 ∧ 2 + 2 = 4 := by
  constructor
  · trivial
  Let's prove that 2 + 2 = 4
    norm_num    ← shortcut: decide closes here
    rfl
```

**After**:
```lean
example : 1 + 1 = 2 ∧ 2 + 2 = 4 := by
  constructor
  · trivial
  norm_num    ← now step 1 (was step 2)
  rfl
```

### Expected behavior
- `check` mode: shortcut at `{exercise: "example", stepNumber: 2}` is **stale** (no longer
  triggered at step 2). The new `norm_num` at step 1 is **unexpected** (not in test file).
- `update` mode:
  - Stale entry prompt:
    ```
    Stale: [example: step 2] — `norm_num` no longer closes goal at step 2
    Remove? [y/N]
    ```
  - New shortcut prompt:
    ```
    Shortcut [example: step 1] — `norm_num` closes goal at "rfl"
    Accept? [y/N]
    ```

---

## 6. Step Boundary Insertion — New Step Created

### Input
Teacher inserts a new `Let's prove that` step, splitting an existing step.

**Before**:
```lean
example : 1 + 1 = 2 ∧ 2 + 2 = 4 := by
  constructor
  · trivial
  Let's prove that 2 + 2 = 4
    norm_num    ← shortcut at step 2
    rfl
```

**After**:
```lean
example : 1 + 1 = 2 ∧ 2 + 2 = 4 := by
  constructor
  · trivial
  Let's prove that 2 + 2 = 4
    norm_num    ← now step 2 (unchanged)
  Let's prove that 3 + 3 = 6
    decide      ← new step 3
```

### Expected behavior
- `check` mode: shortcut at step 2 still matches → **expected**.
- No stale entries. The `decide` at step 3 is unexpected (not in test file).

---

## 7. Tactic Text Change — Shortcut No Longer Matches

### Input
Teacher rewrites a tactic's text (e.g., replaces `decide` with `trivial`).

**Before**:
```lean
Let's prove that 2 + 2 = 4
  decide    ← shortcut recorded
```

**After**:
```lean
Let's prove that 2 + 2 = 4
  trivial   ← tactic text changed
```

### Expected behavior
- `check` mode: shortcut `{exercise, stepNumber, tactic: "decide"}` does not match
  `tactic: "trivial"` → **unexpected**. The original entry is **stale**.
- `update` mode: stale entry removed, new shortcut offered for acceptance.

---

## 8. Two Shortcuts at Same Step, Same Tactic

### Input
A proof with two identical tactics at the same step, both closing goals.

```lean
example : 1 + 1 = 2 ∧ 2 + 2 = 4 ∧ 3 + 3 = 6 := by
  constructor
  · trivial
  constructor
  · trivial          ← both `trivial` at step 2
  · decide
```

### Expected behavior
- Both `trivial` shortcuts at step 2 map to the same `{exercise, stepNumber: 2, tactic: "trivial"}`.
- The matching is one-to-one in `.test.json` (only one entry per unique key).
- If one `trivial` is removed, the remaining one at step 2 still matches.

---

## 9. Nested Verbose Proofs

### Input
Waterproof proofs with nested `Let's prove that` blocks.

```lean
example : ∀ n, n + 0 = n := by
  intro n
  induction n with
  | zero =>
    Let's prove that 0 + 0 = 0
      decide          ← outer shortcut
  | succ n ih =>
    Let's prove that n + 1 = n + 1
      rw [Nat.add_succ]  ← inner shortcut
      decide              ← inner shortcut
```

### Expected behavior
- Nested `Let's prove that` blocks produce their own `stepNumber` counters.
- The outer proof and inner proof have separate step numbering (outer step 1, inner step 1).
- `tacticIndexInStep` counts tactics within each block independently.

### `.test.json`
```json
{
  "shortcuts": [
    { "exercise": "example", "stepNumber": 1, "tacticIndexInStep": 1, "tactic": "decide" },
    { "exercise": "example", "stepNumber": 1, "tacticIndexInStep": 1, "tactic": "decide" }
  ],
  "lint": []
}
```

---

## 10. Multiple Proofs in One `#doc` Block

### Input
A single declaration with multiple exercises in a documentation block.

```lean
#doc
  theorem ex1 : 1 + 1 = 2 := by
    trivial
    Let's prove that 1 + 1 = 2
      decide

  theorem ex2 : 2 + 2 = 4 := by
    trivial
    Let's prove that 2 + 2 = 4
      decide
```

### Expected behavior
- Both exercises get their own `stepNumber: 1` — **this is the fix for the old `proofStartLine` bug**.
- Before: `ex2` would get offset step numbers because `proofStartLine` was per-declaration,
  not per-exercise.
- After: step counters reset at each `Exercise "name"` boundary.

### `.test.json`
```json
{
  "shortcuts": [
    { "exercise": "ex1", "stepNumber": 1, "tacticIndexInStep": 2, "tactic": "decide" },
    { "exercise": "ex2", "stepNumber": 1, "tacticIndexInStep": 2, "tactic": "decide" }
  ],
  "lint": []
}
```

### Check
Both shortcuts match independently. `check` reports 2 expected shortcuts.

---

## 11. Lint Fuzzy Matching — Position Shifted ±5 Lines

### Input
Teacher adds a comment or blank line before a lint-violating tactic.

**Before**:
```lean
theorem ex : 1 + 1 = 2 := by
  Fix x : Nat  ← B2 lint violation (line 2)
  trivial
```

**After** (teacher added comment on line 2):
```lean
theorem ex : 1 + 1 = 2 := by
  -- some comment
  Fix x : Nat  ← B2 lint violation (line 3)
  trivial
```

### Expected behavior
- `classifyLint` finds B2 at line 3 but the expected entry is at line 2.
- Fuzzy search (±5 lines) finds `Fix` at line 3 with the same tactic token.
- `check` mode: classified as **expected** (fuzzy matched).
- `update` mode: position updated from line 2 to line 3 with teacher confirmation.

---

## 12. Lint Fuzzy Matching — No Match Beyond ±5 Lines

### Input
Teacher deletes 10 lines before a lint-violating tactic.

**Before**: B2 violation at line 10
**After**: B2 violation at line 0 (or doesn't exist)

### Expected behavior
- Fuzzy search ±5 lines finds nothing matching the same check + tactic.
- `check` mode: classified as **unexpected** (new lint violation).
- `update` mode: new lint entry offered for acceptance.

---

## 13. Mixed Verbose and Non-Verbose Proofs in Same File

### Input
```lean
-- TestSuite/Fixtures/Mixed.lean
theorem verboseEx : 1 + 1 = 2 ∧ 2 + 2 = 4 := by
  constructor
  · trivial
  Let's prove that 2 + 2 = 4
    norm_num    ← shortcut

theorem plainEx : 3 + 3 = 6 := by
  decide        ← no shortcut (non-Verbose)
```

### Expected behavior
- `update` produces 1 shortcut for `verboseEx` and 0 for `plainEx`.
- `.test.json` only contains the `verboseEx` shortcut.

---

## 14. Fresh Regeneration (No Backward Compat)

### Input
An old `.test.json` with `lineInProof` field:
```json
{
  "shortcuts": [
    {
      "exercise": "example",
      "lineInProof": 2,
      "tactic": "decide"
    }
  ],
  "lint": []
}
```

### Expected behavior
- `update --all` completely regenerates `.test.json` from scratch.
- The old `lineInProof` field is not read or written.
- The new `.test.json` has `stepNumber` and `tacticIndexInStep`.

### `.test.json` after regeneration
```json
{
  "shortcuts": [
    {
      "exercise": "example",
      "stepNumber": 1,
      "tacticIndexInStep": 2,
      "tactic": "decide"
    }
  ],
  "lint": []
}
```

---

## 15. Display Format — Tactic Text in Prompts

### Expected prompts (from `update` mode)

**New shortcut**:
```
Shortcut [example: step 2] — `norm_num` closes goal at "rfl"
Accept? [y/N]
```

**Stale shortcut**:
```
Stale: [example: step 1] — `trivial` no longer closes goal at step 1
Remove? [y/N]
```

**Lint entry**:
```
Lint [B2] at line 15 — `Fix x : Nat` (type annotation)
Accept? [y/N]
```

**Expected (from `check` mode)**:
```
✓ example: step 2 — `norm_num` (expected)
✓ example: step 1 — `trivial` (expected)
```

**Unexpected (from `check` mode)**:
```
⚠ example: step 3 — `decide` (unexpected)
```

**Stale (from `check` mode)**:
```
⚠ example: step 1 — `trivial` (stale, in test file but not triggered)
```

---

## 16. Edge Case — Proof with Single Step, Single Tactic

### Input
```lean
example : 1 + 1 = 2 := by
  decide
```

### Expected behavior
- `stepNumber = 1`, `tacticIndexInStep = 1`.
- No step boundary in the file, but this is a Verbose proof? **No** — this proof has
  no `Let's prove that` boundary, so it's **not** a Verbose proof and produces **no**
  shortcut entry.

---

## 17. Edge Case — Verbose Proof with Empty Step

### Input
```lean
example : 1 + 1 = 2 ∧ 2 + 2 = 4 := by
  constructor
  · trivial
  Let's prove that 2 + 2 = 4
  -- no tactics in this step
  decide
```

### Expected behavior
- The empty step produces no tactics and no `tacticIndexInStep` values.
- `decide` is the first tactic of step 2 (or step 3 if the empty step counts).
- Behavior depends on whether empty steps increment `stepNumber`. **Decision**: empty
  steps do increment `stepNumber` (the `Let's prove that` boundary exists).

---

## Test File Naming Convention

Tests should use fixture files following this convention:

| Test # | Fixture File | Purpose |
|--------|-------------|---------|
| 1 | `BasicVerbose.lean` | Simple 2-step Verbose proof |
| 2 | `PlainProof.lean` | Non-Verbose proof |
| 3 | `MultiExercise.lean` | Multiple exercises in one file |
| 4 | `WithinStepInsert.lean` | Before/after for test 4 |
| 5 | `RemoveStepBoundary.lean` | Before/after for test 5 |
| 6 | `InsertStepBoundary.lean` | Before/after for test 6 |
| 7 | `TacticChange.lean` | Before/after for test 7 |
| 8 | `SameTacticSameStep.lean` | Two identical tactics at same step |
| 9 | `NestedVerbose.lean` | Nested `Let's prove that` blocks |
| 10 | `DocBlockMultiEx.lean` | Multiple exercises in one `#doc` block |
| 11 | `LintFuzzyNear.lean` | Lint position shifted <5 lines |
| 12 | `LintFuzzyFar.lean` | Lint position shifted >5 lines |
| 13 | `MixedVerbosePlain.lean` | Both Verbose and non-Verbose proofs |
| 14 | `OldFormat.lean` | Fixture for backward compat removal |
| 16 | `SingleTactic.lean` | Non-Verbose single tactic |
| 17 | `EmptyStep.lean` | Verbose proof with empty step |
