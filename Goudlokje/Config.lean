import Lean.Data.Json
import Lean.Data.Json.FromToJson

namespace Goudlokje

/-- Project-wide configuration loaded from `.goudlokje.json`. -/
structure Config where
  /-- Tactic strings to probe at each proof step. -/
  tactics : Array String
  /-- When true, restrict shortcut reporting to the first tactic position within
      each Lean Verbose step body, suppressing sub-step noise. -/
  filterVerboseSteps : Bool := false
  deriving Repr, Inhabited, BEq

instance : Lean.FromJson Config where
  fromJson? json := do
    let tactics ← Lean.fromJson? (← json.getObjVal? "tactics")
    let filterVerboseSteps :=
      (json.getObjVal? "filterVerboseSteps").toOption
        |>.bind (Lean.fromJson? · |>.toOption) |>.getD false
    return { tactics, filterVerboseSteps }

instance : Lean.ToJson Config where
  toJson cfg :=
    Lean.Json.mkObj [
      ("tactics",            Lean.toJson cfg.tactics),
      ("filterVerboseSteps", Lean.toJson cfg.filterVerboseSteps)
    ]

/-- Load a Config from a `.goudlokje.json` file. -/
def Config.load (path : System.FilePath) : IO Config := do
  let contents ← IO.FS.readFile path
  let json ← IO.ofExcept (Lean.Json.parse contents)
  IO.ofExcept (Lean.fromJson? json)

end Goudlokje
