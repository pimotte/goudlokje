import Goudlokje.Analysis
import Goudlokje.TestFile

namespace Goudlokje

/-- Classification of a found probe result against the expected shortcuts. -/
inductive ShortcutResult where
  /-- Shortcut found and NOT listed in the test file — error in check mode. -/
  | unexpected (r : ProbeResult)
  /-- Shortcut found and listed in the test file — OK. -/
  | expected   (r : ProbeResult)
  deriving Repr, Inhabited

/-- Listed in the test file but the tactic no longer closes the goal — warning. -/
structure StaleEntry where
  entry : ExpectedShortcut
  deriving Repr

structure ClassificationResult where
  shortcuts : Array ShortcutResult
  stale     : Array StaleEntry
  deriving Repr

/-- Classify probe results against expected shortcuts in the test file. -/
def classify (found : Array ProbeResult) (tf : TestFile) : ClassificationResult :=
  let matchesEntry (r : ProbeResult) (e : ExpectedShortcut) : Bool :=
    e.file == r.file && e.line == r.line && e.column == r.column && e.tactic == r.tactic
  let shortcuts := found.map fun r =>
    if tf.expected.any (matchesEntry r) then .expected r else .unexpected r
  let stale := tf.expected.filterMap fun e =>
    if found.any (fun r => matchesEntry r e) then none
    else some { entry := e }
  { shortcuts, stale }

/-- Pretty-print a single ShortcutResult to stdout. -/
def printShortcutResult (r : ShortcutResult) : IO Unit :=
  match r with
  | .unexpected p =>
    IO.eprintln s!"ERROR: unexpected shortcut at {p.file}:{p.line}:{p.column} — tactic `{p.tactic}` closes the goal"
  | .expected p =>
    IO.println s!"OK: expected shortcut at {p.file}:{p.line}:{p.column} — tactic `{p.tactic}`"

/-- Pretty-print a stale entry warning to stdout. -/
def printStaleEntry (s : StaleEntry) : IO Unit :=
  IO.eprintln s!"WARN: stale entry in test file — {s.entry.file}:{s.entry.line}:{s.entry.column} tactic `{s.entry.tactic}` no longer closes the goal"

end Goudlokje
