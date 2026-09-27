import Lean.Environment
import Goudlokje.Options

/-!
# Syntax origin

Classifies syntax kinds by the module that declares their parser. This replaces hand-maintained
lists of kind names: a tactic is a Lean Verbose tactic exactly when its parser lives in one of the
modules configured by `goudlokje.verboseModules` (by default the `Verbose.*` modules).
-/

namespace Goudlokje

open Lean

/-- The module that declares the parser for `kind`, if it is imported. -/
def kindModule? (env : Environment) (kind : SyntaxNodeKind) : Option Name :=
  (env.getModuleIdxFor? kind).bind (env.header.moduleNames[·]?)

/-- The module name prefixes configured by `goudlokje.verboseModules`. -/
def verboseModules (opts : Options) : Array Name :=
  (splitListOption (goudlokje.verboseModules.get opts)).map String.toName

/-- Whether the parser for `kind` is declared in one of the `modules` (see `verboseModules`). -/
def isVerboseKind (env : Environment) (modules : Array Name) (kind : SyntaxNodeKind) : Bool :=
  (kindModule? env kind).any fun m => modules.any (·.isPrefixOf m)

end Goudlokje
