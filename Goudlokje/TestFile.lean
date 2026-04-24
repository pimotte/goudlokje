import Lean.Data.Json
import Lean.Data.Json.FromToJson

namespace Goudlokje

/-- A shortcut recorded as expected in the `.test.json` companion file. -/
structure ExpectedShortcut where
  exercise    : String
  lineInProof : Nat
  tactic      : String
  deriving Repr, BEq, Inhabited

/-- A lint violation documented as expected (suppressed) in the `.test.json` companion file. -/
structure ExpectedLintViolation where
  file    : String
  line    : Nat
  column  : Nat
  check   : String
  message : String
  deriving Repr, BEq, Inhabited

/-- The contents of a `.test.json` file accompanying a `.lean` worksheet. -/
structure TestFile where
  expected : Array ExpectedShortcut
  lint     : Array ExpectedLintViolation := #[]
  deriving Repr, Inhabited, BEq

instance : Lean.FromJson ExpectedShortcut where
  fromJson? json := do
    return {
      exercise    := ← Lean.fromJson? (← json.getObjVal? "exercise")
      lineInProof := ← Lean.fromJson? (← json.getObjVal? "lineInProof")
      tactic      := ← Lean.fromJson? (← json.getObjVal? "tactic")
    }

instance : Lean.ToJson ExpectedShortcut where
  toJson s := Lean.Json.mkObj [
    ("exercise",    Lean.toJson s.exercise),
    ("lineInProof", Lean.toJson s.lineInProof),
    ("tactic",      Lean.toJson s.tactic)
  ]

instance : Lean.FromJson ExpectedLintViolation where
  fromJson? json := do
    return {
      file    := ← Lean.fromJson? (← json.getObjVal? "file")
      line    := ← Lean.fromJson? (← json.getObjVal? "line")
      column  := ← Lean.fromJson? (← json.getObjVal? "column")
      check   := ← Lean.fromJson? (← json.getObjVal? "check")
      message := ← Lean.fromJson? (← json.getObjVal? "message")
    }

instance : Lean.ToJson ExpectedLintViolation where
  toJson v := Lean.Json.mkObj [
    ("file",    Lean.toJson v.file),
    ("line",    Lean.toJson v.line),
    ("column",  Lean.toJson v.column),
    ("check",   Lean.toJson v.check),
    ("message", Lean.toJson v.message)
  ]

instance : Lean.FromJson TestFile where
  fromJson? json := do
    let expected ← Lean.fromJson? (← json.getObjVal? "expected")
    -- "lint" field is optional for backward compatibility with old test.json files.
    let lint ← match json.getObjVal? "lint" with
      | .ok v  => Lean.fromJson? v
      | .error _ => pure #[]
    return { expected, lint }

instance : Lean.ToJson TestFile where
  toJson tf := Lean.Json.mkObj [
    ("expected", Lean.toJson tf.expected),
    ("lint",     Lean.toJson tf.lint)
  ]

/-- Load a TestFile; returns an empty TestFile if the file does not exist. -/
def TestFile.load (path : System.FilePath) : IO TestFile := do
  if !(← path.pathExists) then return { expected := #[] }
  let contents ← IO.FS.readFile path
  let json ← IO.ofExcept (Lean.Json.parse contents)
  IO.ofExcept (Lean.fromJson? json)

/-- Persist a TestFile to disk as pretty-printed JSON. -/
def TestFile.save (tf : TestFile) (path : System.FilePath) : IO Unit :=
  IO.FS.writeFile path (Lean.Json.pretty (Lean.toJson tf) ++ "\n")

end Goudlokje
