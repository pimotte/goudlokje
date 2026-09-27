import Lean.Linter.Init

/-!
# Options

All Goudlokje settings are Lean options. Set them per project in the lakefile, with the `weak.`
prefix so that modules that do not import Goudlokje accept them:

```lean
lean_lib Worksheets where
  leanOptions := #[⟨`weak.linter.goudlokje.explain, true⟩]
```
-/

namespace Goudlokje

register_option linter.goudlokje.explain : Bool := {
  defValue := false
  descr := "(Goudlokje) report the proof steps Goudlokje finds in each command, for debugging"
}

register_option linter.goudlokje.shortcut : Bool := {
  defValue := true
  descr := "(Goudlokje) report steps where a probe tactic (`goudlokje.probes`) closes the goal \
    before the end of the proof"
}

register_option linter.goudlokje.rawTactic : Bool := {
  defValue := true
  descr := "(Goudlokje) report raw Lean tactics in Verbose proofs, except those allowed by \
    `goudlokje.allowedTactics` (B1)"
}

register_option linter.goudlokje.typeAscription : Bool := {
  defValue := true
  descr := "(Goudlokje) report type annotations in proof steps: `(e : T)` and `Fix x : T` (B2)"
}

register_option linter.goudlokje.sorry : Bool := {
  defValue := true
  descr := "(Goudlokje) report `sorry` in exercises that do not allow it (B3)"
}

register_option goudlokje.allowedTactics : String := {
  defValue := ""
  descr := "(Goudlokje) raw Lean tactics allowed in Verbose proofs, as `;;`-separated leading \
    tokens, e.g. \"norm_num;; rfl\""
}

register_option goudlokje.verboseModules : String := {
  defValue := "Verbose"
  descr := "(Goudlokje) the modules whose tactics count as Lean Verbose tactics, as `;;`-separated \
    module name prefixes, e.g. \"Verbose;; MyProject.Tactics\""
}

register_option goudlokje.probes : String := {
  defValue := ""
  descr := "(Goudlokje) the probe tactics, separated by `;;`, e.g. \"decide;; simp;; norm_num\""
}

register_option goudlokje.probeHeartbeats : Nat := {
  defValue := 100
  descr := "(Goudlokje) the heartbeat budget of a single probe, in thousands (like \
    `maxHeartbeats`); a probe that runs out does not count as a shortcut"
}

/-- Splits a `;;`-separated list option (such as `goudlokje.probes`) into its trimmed, non-empty
    items. -/
def splitListOption (value : String) : Array String :=
  (value.splitOn ";;").toArray.filterMap fun item =>
    let item := item.trimAscii.toString
    if item.isEmpty then none else some item

end Goudlokje
