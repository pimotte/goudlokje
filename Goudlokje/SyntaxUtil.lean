import Lean.Syntax

/-! Small helpers for inspecting syntax. -/

namespace Goudlokje

open Lean

/-- All nodes of kind `kind` in `stx`, outermost first. -/
partial def findAllOfKind (stx : Syntax) (kind : SyntaxNodeKind) : Array Syntax :=
  go stx #[]
where
  go (stx : Syntax) (acc : Array Syntax) : Array Syntax :=
    let acc := if stx.isOfKind kind then acc.push stx else acc
    stx.getArgs.foldl (fun acc child => go child acc) acc

/-- The first token of `stx` (e.g. `exact` for `exact h`), without surrounding whitespace. -/
partial def leadingToken? (stx : Syntax) : Option String :=
  match stx with
  | .atom _ val => some val.trimAscii.toString
  | .ident _ rawVal _ _ => some rawVal.toString
  | .node _ _ args => args.findSome? leadingToken?
  | .missing => none

/-- Whether `stx` contains the atom `val`. -/
partial def hasAtom (stx : Syntax) (val : String) : Bool :=
  match stx with
  | .atom _ v => v.trimAscii == val
  | .node _ _ args => args.any (hasAtom · val)
  | _ => false

end Goudlokje
