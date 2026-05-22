import Lean.Data.Json
import Lean.Data.Json.FromToJson

namespace Goudlokje

/-- Project-wide configuration loaded from `.goudlokje.json`. -/
structure Config where
  /-- Tactic strings to probe at each proof step. -/
  tactics : Array String
  deriving Repr, Inhabited, BEq

instance : Lean.FromJson Config where
  fromJson? json := do
    let tactics ← Lean.fromJson? (← json.getObjVal? "tactics")
    return { tactics }

instance : Lean.ToJson Config where
  toJson cfg :=
    Lean.Json.mkObj [
      ("tactics", Lean.toJson cfg.tactics)
    ]

/-- Load a Config from a `.goudlokje.json` file. -/
def Config.load (path : System.FilePath) : IO Config := do
  let contents ← IO.FS.readFile path
  let json ← IO.ofExcept (Lean.Json.parse contents)
  IO.ofExcept (Lean.fromJson? json)

end Goudlokje
