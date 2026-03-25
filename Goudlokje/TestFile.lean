import Lean.Data.Json
import Lean.Data.Json.FromToJson

namespace Goudlokje

/-- A shortcut recorded as expected in the `.test.json` companion file. -/
structure ExpectedShortcut where
  file   : String
  line   : Nat
  column : Nat
  tactic : String
  deriving Repr, BEq, Inhabited

/-- The contents of a `.test.json` file accompanying a `.lean` worksheet. -/
structure TestFile where
  expected : Array ExpectedShortcut
  deriving Repr, Inhabited, BEq

instance : Lean.FromJson ExpectedShortcut where
  fromJson? json := do
    return {
      file   := ← Lean.fromJson? (← json.getObjVal? "file")
      line   := ← Lean.fromJson? (← json.getObjVal? "line")
      column := ← Lean.fromJson? (← json.getObjVal? "column")
      tactic := ← Lean.fromJson? (← json.getObjVal? "tactic")
    }

instance : Lean.ToJson ExpectedShortcut where
  toJson s := Lean.Json.mkObj [
    ("file",   Lean.toJson s.file),
    ("line",   Lean.toJson s.line),
    ("column", Lean.toJson s.column),
    ("tactic", Lean.toJson s.tactic)
  ]

instance : Lean.FromJson TestFile where
  fromJson? json := do
    return { expected := ← Lean.fromJson? (← json.getObjVal? "expected") }

instance : Lean.ToJson TestFile where
  toJson tf := Lean.Json.mkObj [("expected", Lean.toJson tf.expected)]

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
