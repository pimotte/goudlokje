# Goudlokje

Goudlokje helps teachers keep Lean worksheets with reference solutions *just right*: not
incorrect, and not too easy. It checks exercises written with
[Lean Verbose](https://github.com/PatrickMassot/verbose-lean4), in
[Waterproof](https://github.com/impermeable/waterproof-genre) worksheets:

| Check            | Reports                                                                                   | Severity |
|------------------|-------------------------------------------------------------------------------------------|----------|
| `shortcut`       | a *probe* tactic (e.g. `decide`) closes a goal before the end of the proof, so the exercise can be shortcut | error    |
| `rawTactic`      | a raw Lean tactic (e.g. `exact`) instead of a Verbose tactic                              | error    |
| `typeAscription` | a type annotation, `(e : T)` or `Fix x : T`                                               | warning  |
| `sorry`          | a `sorry` or `admit`                                                                      | error    |

The checks are Lean linters: they run while Lean elaborates the worksheet, during `lake build`
and in the editor. Only exercises written with Verbose (a Verbose `Exercise`/`Example`, or a
proof using Verbose tactics) are checked, and only in student input areas (between `:::input` and
`:::`).

Findings that are intended, for example a shortcut the reference solution cannot avoid, are
recorded per worksheet in a `.test.json` file and are then no longer reported.

---

## Setting up a worksheet project

Goudlokje requires the Lean toolchain in `lean-toolchain`; your project must use the same one.
Goudlokje itself depends only on Lean (and `Cli` for its command); the worksheet project brings
Lean Verbose, the Waterproof genre and Mathlib, in the versions it chooses.

1. Add Goudlokje as a dependency in `lakefile.lean`:

   ```lean
   require "goudlokje" from git "https://github.com/pimotte/goudlokje" @ "main"
   ```

   Also add `/.lake` to `.gitignore` if it is not there yet: Goudlokje keeps its results in
   `.lake/goudlokje` (see below).

2. Make the worksheets modules of a library and configure the checks through its options. The
   `weak.` prefix keeps modules that do not import Goudlokje from rejecting the options.

   ```lean
   lean_lib Worksheets where
     leanOptions := #[
       ⟨`weak.goudlokje.probes, "decide;; tauto;; omega;; norm_num;; simp"⟩,
       ⟨`weak.goudlokje.allowedTactics, "norm_num"⟩
     ]
   ```

3. Import Goudlokje in every worksheet, or better, in one module that all worksheets import
   (a "sheet header" with the imports every worksheet needs):

   ```lean
   import Goudlokje
   import Verbose.English.All
   import WaterproofGenre
   ```

Then `lake build` checks the worksheets, and the editor shows the findings.

### Options

| Option                                   | Default | Meaning                                                                                      |
|------------------------------------------|---------|----------------------------------------------------------------------------------------------|
| `goudlokje.probes`                       | `""`    | Probe tactics, separated by `;;`. Without probes, the `shortcut` check does not run.         |
| `goudlokje.probeHeartbeats`              | `100`   | Heartbeat budget per probe, in thousands (like `maxHeartbeats`). A probe that runs out is not a shortcut. |
| `goudlokje.allowedTactics`               | `""`    | Raw Lean tactics allowed in Verbose proofs, as leading tokens separated by `;;`, e.g. `"norm_num;; rfl"`. |
| `goudlokje.verboseModules`               | `"Verbose"` | The modules whose tactics count as Lean Verbose tactics, as module name prefixes separated by `;;`. Add the modules of your own Verbose-style tactics, e.g. `"Verbose;; MyProject.Tactics"`; keep `Verbose` in the list. |
| `linter.goudlokje.shortcut`, `.rawTactic`, `.typeAscription`, `.sorry` | `true` | Turn a check on or off.                 |
| `linter.goudlokje.explain`               | `false` | Debugging aid: shows the steps Goudlokje finds in each command and how it groups them.       |

Like any option, they can also be set in a file (`set_option … in` for a single exercise).

---

## Shortcuts

A *step* is a tactic in the proof as the student writes it. Goudlokje tries the probe tactics on
the goal of every step that does not itself close that goal: at a step that does, the student has
to write a step anyway, so a probe there saves nothing. In particular, the last step of a proof is
never a shortcut, and a one-step proof has none.

Steps that work on the same goal (for example `Let's now prove that P`, then `show P`, then the
step that proves it) form a *chain*. Per chain only the first step where some probe closes the
goal is reported, with every probe that closes it there.

Lean Verbose blocks the remaining goals until the student starts on them (`Let's now prove
that …`), so most probes cannot close them earlier. `tauto` can see through the block and may
report a shortcut at `Let's now prove that`.

---

## Expected findings: `.test.json`

Each worksheet `Sheet.lean` may have a `Sheet.test.json`, listing per exercise what is expected:

```json
{
  "exercises": {
    "1.1.13": {
      "allowSorry": true,
      "lint": [
        {"check":"typeAscription","step":3}
      ],
      "shortcuts": [
        {"step":1,"tactic":"decide"}
      ]
    }
  },
  "testJsonVersion": 3
}
```

- **Exercises** are identified by the title of a Verbose `Exercise`/`Example`, the name of a
  theorem, or the statement of an anonymous `example` (such as `"example : 1 + 1 = 2"`).
- **Steps** are numbered by position among the steps of the exercise, starting at 1 (nested steps,
  e.g. in a bullet, count too). So they stay valid when other parts of the file change, and when
  blank lines or comments are added inside the exercise. `linter.goudlokje.explain` shows the
  numbers.
- **`allowSorry`** allows `sorry` in an exercise, e.g. in a true-or-false exercise whose statement
  is false.
- **`rawTactic` findings cannot be recorded.** Allow a tactic for the whole project with
  `goudlokje.allowedTactics` instead.

Expectations that no longer occur are reported as stale (warning). Rather than editing the file by
hand, use `goudlokje update`.

---

## The `goudlokje` command

Run it in the worksheet project with `lake exe goudlokje`. Both commands take worksheets or
directories (default: the current directory).

- **`goudlokje check [paths…]`** builds the worksheets and fails if something unexpected is found.
  This is `lake build` plus one thing: Lake does not notice a changed (or deleted) `.test.json`,
  so for worksheets whose `.test.json` changed since they were built, `check` compares the
  recorded results (see below) with the current `.test.json` instead of rebuilding them.
- **`goudlokje update [--all] [paths…]`** builds the worksheets and updates their `.test.json`
  from the recorded results. It records new findings as expected and removes stale expectations,
  including those of exercises that no longer exist. It asks before each change; with `--all` it
  makes them all. Exercises that do not elaborate keep their expectations.

Neither command rebuilds worksheets that are up to date. Whenever a worksheet is checked on the
command line (`lake build`, `lake lean`), Goudlokje records everything it found in
`.lake/goudlokje/<module>.jsonl`, together with hashes of the source and of the `.test.json` it
was checked against. If these results are missing (e.g. after deleting
`.lake/goudlokje`), `update` recomputes them with `lake lean`, which does not touch the build, and
so does `check` for worksheets with a `.test.json`. So pass `update` only worksheets: other modules
never have results and are elaborated again every time. The language server does not record
results.

### CI

```yaml
- name: Check worksheets
  run: lake exe goudlokje check
```

A plain `lake build` of the worksheets is also a valid check, since unexpected findings are
errors.

---

## Development

```bash
lake build          # the linters and the goudlokje executable
lake test           # unit tests of the linters (runs `lake test` in the test package)
test/e2e/run.sh     # end-to-end tests of the commands, and a regression test of all findings
```

The tests are a separate Lake package in `test/` (library `GoudlokjeTests`), because they need
Lean Verbose, the Waterproof genre and Mathlib, which Goudlokje itself does not depend on. Before
the first run, get the Mathlib cache there: `cd test && lake exe cache get`.

`test/e2e/run.sh` checks the fixtures in `test/e2e/fixtures` and compares everything found with
`test/e2e/fixtures/expected`. After an intended change of behaviour, run
`test/e2e/run.sh --regenerate` and review the diff.

Code overview (`Goudlokje/`):

| Module                      | Contents                                                                    |
|-----------------------------|-----------------------------------------------------------------------------|
| `Steps`, `Origin`           | proof steps from the syntax and info trees; Verbose or not, by the module that declares a tactic (`goudlokje.verboseModules`) |
| `Scope`, `Exercise`         | input areas; the per-command context shared by the checks                   |
| `Check`, `Finding`          | the checks and their properties; the issues they find                       |
| `Probe`, `Checks/`          | running probes with a budget; the four checks                               |
| `Linter`, `Report`          | the linter: messages, stale entries, the results files                      |
| `Expectations`              | the `.test.json` format; which findings are expected, which entries stale    |
| `Cli/`                      | the `check` and `update` commands; reading the results files                |
