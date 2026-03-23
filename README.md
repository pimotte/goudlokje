# Goudlokje

A Lean 4 tool that helps teachers verify that worksheet exercises are neither incorrect nor trivially solvable.

It runs configurable tactics at every proof step in a worksheet and reports any **shortcuts** — places where a tactic closes a goal before the intended end of the proof. This lets you catch exercises that are accidentally too easy.

---

## How it works

1. You configure which tactics to probe in `.goudlokje.json`.
2. Goudlokje elaborates each `.lean` file and tries each probe tactic at every goal state.
3. Results are compared against a per-file `.test.json` that records *expected* shortcuts (e.g. in the reference solution itself).
4. Any *unexpected* shortcut causes `check` to exit non-zero, failing CI.

---

## Installation

### As a Lake dependency (recommended)

Add Goudlokje as a dependency in your project's `lakefile.lean`:

```lean
require "goudlokje"
  from git "https://github.com/pimotte/goudlokje" @ "main"
```

Then build the executable (Lake will fetch and compile Goudlokje automatically):

```bash
lake build goudlokje
```

The binary is placed at `.lake/packages/goudlokje/.lake/build/bin/goudlokje`.

### Standalone build

```bash
git clone https://github.com/pimotte/goudlokje
cd goudlokje
lake build goudlokje
```

The binary is placed at `.lake/build/bin/goudlokje`.

### Toolchain

Goudlokje is pinned to the Lean toolchain in `lean-toolchain`. Your project must use the same toolchain version.

---

## Configuration

Create a `.goudlokje.json` file at the root of your project:

```json
{
  "tactics": ["decide", "tauto", "omega"],
  "filterVerboseSteps": false
}
```

| Field                | Type            | Default | Description                                                                                                   |
|----------------------|-----------------|---------|---------------------------------------------------------------------------------------------------------------|
| `tactics`            | array of string | `[]`    | Tactic expressions to probe at every goal in every proof                                                      |
| `filterVerboseSteps` | bool            | `false` | When `true`, only the first tactic in each Lean Verbose step body is probed, suppressing sub-step noise       |

**Shortcut semantics:** A probe tactic only counts as a shortcut if it can close the goal at a position that is *not* the last step of its proof. Shortcuts at the final proof step are never reported — the student must still write that step, so it saves no lines. This means single-step proofs never produce shortcuts.

**Lean Verbose `Exercise`/`Example` blocks:** Goudlokje automatically ignores synthetic tactic containers (`by` blocks, tactic-sequence wrappers, and the `with_suggestions`/`without_suggestions` wrappers inserted by the Verbose `Exercise`/`Example` command at the `Proof:` token position). Only the individual user-written tactics inside the `Proof: … QED` body are probed. This filtering is always active; no configuration is needed.

> **Example:** A two-line proof `step1; step2` reports a shortcut only if a probe closes the goal at `step1` (saving `step2`). If the probe also happens to work at `step2`, that is *not* reported since the student must write that line anyway.

If `.goudlokje.json` is absent, Goudlokje runs with no probe tactics (no shortcuts can be found).

---

## Usage

### `check` — validate worksheets (for CI)

```bash
# Check all .lean files in the current directory (recursively)
goudlokje check

# Check specific files or directories
goudlokje check Exercises/ Solutions/Sheet1.lean

# Print debug information (probe counts, result statistics)
goudlokje check --debug Exercises/

# Print per-probe verbose output (implies --debug)
goudlokje check --verbose Exercises/
```

Exits **0** if no unexpected shortcuts are found, **1** otherwise.

> **Tip:** Always invoke Goudlokje via `lake exe goudlokje` so that Lake sets up the Lean search path correctly for all project imports. Running the binary directly may cause imports to fail silently and produce 0 results. In `--debug` mode a warning is printed when no tactic positions are found in a file.

### `update` — record expected shortcuts

```bash
# Interactive: prompt for each found shortcut
goudlokje update Exercises/

# Non-interactive: accept all shortcuts without prompting
goudlokje update --all Exercises/

# With debug output
goudlokje update --debug --all Exercises/

# With per-probe verbose output
goudlokje update --verbose --all Exercises/
```

`update` reads existing `.test.json` files, shows new shortcuts and stale entries, and writes the updated file back to disk.

---

## Expected shortcuts (`.test.json`)

Each `.lean` file may have an accompanying `<filename>.test.json` that lists shortcuts which are *expected* (i.e. intentional or unavoidable). Goudlokje ignores these when running `check`.

Example `Sheet1.test.json`:

```json
{
  "expected": [
    { "file": "Sheet1.lean", "line": 12, "column": 4, "tactic": "decide" }
  ]
}
```

Use `goudlokje update --all` to generate these files automatically from found shortcuts.

---

## Running the test suite

```bash
lake exe goudlokje_tests
```

The test suite covers:
- Config parsing (`TestSuite/Config.lean`)
- TestFile round-trips (`TestSuite/TestFile.lean`)
- Shortcut classification (`TestSuite/Shortcuts.lean`)
- File discovery (`TestSuite/Discovery.lean`)
- Analysis integration with vanilla Lean, Lean Verbose, and Waterproof Genre fixtures (`TestSuite/Analysis.lean`)
- End-to-end `check` mode (`TestSuite/Check.lean`)
- End-to-end `update --all` mode (`TestSuite/Update.lean`)

---

## Supported proof styles

| Style              | Status |
|--------------------|--------|
| Vanilla Lean 4     | ✅     |
| Lean Verbose       | ✅     |
| Waterproof Genre   | ✅     |

---

## CI integration

### Standalone build

```yaml
- name: Check for shortcuts
  run: |
    lake build goudlokje
    .lake/build/bin/goudlokje check
```

### As a Lake dependency

When Goudlokje is declared as a `require` in your lakefile, the binary is built inside the `.lake/packages/` tree:

```yaml
- name: Check for shortcuts
  run: |
    lake build goudlokje
    .lake/packages/goudlokje/.lake/build/bin/goudlokje check
```

The step fails automatically if any unexpected shortcut is found.
