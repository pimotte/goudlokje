import Lean.Data.Json
import Goudlokje.Options

/-!
# Checks

The checks Goudlokje performs on every exercise, and their properties.
-/

namespace Goudlokje

open Lean

/-- A check performed on every exercise. -/
inductive Check where
  /-- A probe tactic closes a goal before the end of the proof (see `Checks.Shortcut`). -/
  | shortcut
  /-- A raw Lean tactic in a Verbose proof (B1). -/
  | rawTactic
  /-- A type annotation in a proof step (B2). -/
  | typeAscription
  /-- A `sorry` in a proof (B3). -/
  | sorry
  deriving Repr, BEq, Hashable, Inhabited

namespace Check

/-- All checks, in the order they run. -/
def all : Array Check := #[.shortcut, .rawTactic, .typeAscription, .sorry]

/-- The name of the check, as used in `.test.json` and the results file. -/
def name : Check → String
  | .shortcut => "shortcut"
  | .rawTactic => "rawTactic"
  | .typeAscription => "typeAscription"
  | .sorry => "sorry"

/-- The check called `name`, if any. -/
def ofName? (name : String) : Option Check :=
  all.find? (·.name == name)

/-- The option that enables the check. -/
def linterOption : Check → Lean.Option Bool
  | .shortcut => linter.goudlokje.shortcut
  | .rawTactic => linter.goudlokje.rawTactic
  | .typeAscription => linter.goudlokje.typeAscription
  | .sorry => linter.goudlokje.sorry

/-- The severity of an issue that `.test.json` does not expect. -/
def severity : Check → MessageSeverity
  | .typeAscription => .warning
  | _ => .error

/-- Whether issues can be recorded as expected in `.test.json`. -/
def suppressible : Check → Bool
  | .rawTactic => false
  | _ => true

instance : ToJson Check := ⟨(toJson ·.name)⟩

instance : FromJson Check where
  fromJson? json := do
    let name ← json.getStr?
    (ofName? name).elim (throw s!"unknown check `{name}`") pure

end Check

end Goudlokje
