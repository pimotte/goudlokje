import Lean.Data.Json
import Lean.Elab.Command
import Goudlokje.FileCache
import Goudlokje.Check

/-!
# Expectations

The `<worksheet>.test.json` companion file records what is *expected* in a worksheet: shortcuts
that are acceptable and lint findings that are documented, per exercise. Steps are identified by
their position among the steps of the exercise (see `stepNumber`), so edits elsewhere in the file,
and blank lines or comments inside the exercise, do not invalidate them.

```json
{
  "testJsonVersion": 3,
  "exercises": {
    "1.1.13": {
      "shortcuts": [{ "step": 1, "tactic": "decide" }],
      "lint": [{ "check": "typeAscription", "step": 3 }],
      "allowSorry": true
    }
  }
}
```
-/

namespace Goudlokje

open Lean

/-- The current version of the `.test.json` format. Version 3 numbers steps by position instead of
    by line. -/
def testJsonVersion : Nat := 3

/-- A probe tactic that is expected to close the goal at a step. -/
structure ExpectedShortcut where
  step   : Nat
  tactic : String
  deriving Repr, BEq, Hashable, Inhabited, ToJson, FromJson

/-- A documented lint finding at a step. -/
structure ExpectedLint where
  check : String
  step  : Nat
  deriving Repr, BEq, Hashable, Inhabited, ToJson, FromJson

/-- What is expected in one exercise. -/
structure ExerciseExpectations where
  shortcuts  : Array ExpectedShortcut := #[]
  lint       : Array ExpectedLint := #[]
  /-- The exercise may contain `sorry`, e.g. a true-or-false exercise whose statement is false. -/
  allowSorry : Bool := false
  deriving Repr, BEq, Inhabited

/-- Whether `e` expects an issue of `check` at `step` (for shortcuts: of probe `tactic?`). Raw
    tactics cannot be expected (see `Check.suppressible`). -/
def ExerciseExpectations.expects (e : ExerciseExpectations) (check : Check) (step : Nat)
    (tactic? : Option String := none) : Bool :=
  check.suppressible && match check with
  | .shortcut => e.shortcuts.contains { step, tactic := tactic?.getD "" }
  | .sorry => e.allowSorry
  | _ => e.lint.contains { check := check.name, step }

/-- An expectation of an exercise that does not hold (any more). -/
inductive StaleEntry where
  /-- An expected shortcut that no longer occurs. -/
  | shortcut (entry : ExpectedShortcut)
  /-- A documented lint finding that no longer occurs, or that is `invalid`: of a check whose
      findings cannot be expected (see `Check.suppressible`), or of an unknown check. -/
  | lint (entry : ExpectedLint) (invalid : Bool)
  /-- `allowSorry` in an exercise without `sorry`. -/
  | allowSorry
  deriving Repr, BEq

/-- The stale entries of `e`, given the checks that ran on the exercise and what they found, as
    (check, step, probe tactic) triples. Entries of checks that did not run cannot be confirmed, so
    they are not stale; invalid entries always are. -/
def ExerciseExpectations.stale (e : ExerciseExpectations) (ran : Array Check)
    (found : Array (Check × Nat × Option String)) : Array StaleEntry := Id.run do
  let mut stale := #[]
  if ran.contains .shortcut then
    for entry in e.shortcuts do
      unless found.contains (.shortcut, entry.step, some entry.tactic) do
        stale := stale.push (.shortcut entry)
  for entry in e.lint do
    match Check.ofName? entry.check with
    | some check =>
      if !check.suppressible || check == .shortcut || check == .sorry then
        stale := stale.push (.lint entry (invalid := true))
      else if ran.contains check && !found.any fun (c, step, _) => c == check && step == entry.step then
        stale := stale.push (.lint entry (invalid := false))
    | none => stale := stale.push (.lint entry (invalid := true))
  if ran.contains .sorry && e.allowSorry && !found.any (·.1 == .sorry) then
    stale := stale.push .allowSorry
  return stale

/-- The contents of a `.test.json` file. -/
structure Expectations where
  exercises : Std.TreeMap String ExerciseExpectations compare := {}
  deriving Inhabited

/-- Reads field `key` of `json`, or returns `default` if the field is absent. -/
private def optField [FromJson α] (json : Json) (key : String) (default : α) : Except String α :=
  match json.getObjVal? key with
  | .ok value => fromJson? value
  | .error _ => pure default

instance : FromJson ExerciseExpectations where
  fromJson? json := do
    return {
      shortcuts  := ← optField json "shortcuts" #[]
      lint       := ← optField json "lint" #[]
      allowSorry := ← optField json "allowSorry" false
    }

/-- Entries are written sorted by step, so that the file does not depend on the order in which
    they were recorded. -/
instance : ToJson ExerciseExpectations where
  toJson e :=
    let shortcuts := e.shortcuts.qsort fun a b =>
      a.step < b.step || a.step == b.step && a.tactic < b.tactic
    let lint := e.lint.qsort fun a b => a.step < b.step || a.step == b.step && a.check < b.check
    Json.mkObj <|
      (if shortcuts.isEmpty then [] else [("shortcuts", toJson shortcuts)]) ++
      (if lint.isEmpty then [] else [("lint", toJson lint)]) ++
      (if e.allowSorry then [("allowSorry", toJson true)] else [])

instance : FromJson Expectations where
  fromJson? json := do
    let version : Nat ← json.getObjValAs? Nat "testJsonVersion"
      |>.mapError fun _ => "missing `testJsonVersion`"
    unless version == testJsonVersion do
      throw s!"unsupported `testJsonVersion` {version}, expected {testJsonVersion}"
    let exercises ← (← json.getObjVal? "exercises").getObj?
    exercises.foldlM (init := {}) fun acc name value => do
      let e ← fromJson? value |>.mapError (s!"exercise {name.quote}: " ++ ·)
      return { exercises := acc.exercises.insert name e }

instance : ToJson Expectations where
  toJson e := Json.mkObj [
    ("testJsonVersion", toJson testJsonVersion),
    ("exercises", Json.mkObj <| e.exercises.toList.map fun (name, ex) => (name, toJson ex))
  ]

/-- The expectations for exercise `name` (empty if it is not listed). -/
def Expectations.get (e : Expectations) (name : String) : ExerciseExpectations :=
  e.exercises.getD name {}

/-- The companion `.test.json` path of a worksheet. -/
def testJsonPath (worksheet : System.FilePath) : System.FilePath :=
  worksheet.withExtension "test.json"

/-- Parses the contents of a `.test.json` file. -/
def parseExpectations (contents : String) : Except String Expectations := do
  fromJson? (← Json.parse contents)

/-- The contents of the file at `path`, or `none` if it does not exist. -/
def readFile? (path : System.FilePath) : IO (Option String) := do
  unless ← path.pathExists do return none
  return some (← IO.FS.readFile path)

/-- Reads the `.test.json` file at `path`; a missing file means no expectations. -/
def loadExpectations (path : System.FilePath) : IO (Except String Expectations) := do
  let some contents ← readFile? path | return .ok {}
  return parseExpectations contents |>.mapError (s!"{path}: " ++ ·)

/-- A hash of the `.test.json` file at `path` (a missing file hashes like an empty one), to tell
    whether it changed since a worksheet was checked. -/
def expectationsHash (path : System.FilePath) : IO UInt64 :=
  return hash ((← readFile? path).getD "")

/-- Renders JSON for files that people read and diff: object keys sorted, one per line, and the
    elements of arrays one per line in compact form. (`Json.pretty` reverses the order of keys.) -/
partial def renderJson (json : Json) (indent : String := "") : String :=
  let inner := indent ++ "  "
  match json with
  | .obj fields =>
    if fields.isEmpty then "{}" else
    let entries := fields.foldl (init := #[]) fun acc key value =>
      acc.push s!"{inner}{(Json.str key).compress}: {renderJson value inner}"
    "{\n" ++ ",\n".intercalate entries.toList ++ s!"\n{indent}}"
  | .arr items =>
    if items.isEmpty then "[]" else
    "[\n" ++ ",\n".intercalate (items.toList.map (inner ++ ·.compress)) ++ s!"\n{indent}]"
  | json => json.compress

/-- Persists expectations as JSON (see `renderJson`). -/
def saveExpectations (path : System.FilePath) (e : Expectations) : IO Unit :=
  IO.FS.writeFile path (renderJson (toJson e) ++ "\n")

private initialize expectationsCache : FileCache (Except String Expectations) ← IO.mkRef {}

/-- The expectations of the worksheet being elaborated. -/
def getExpectations : Elab.Command.CommandElabM (Except String Expectations) := do
  let path := testJsonPath (← getFileName)
  expectationsCache.get path (loadExpectations path)

end Goudlokje
