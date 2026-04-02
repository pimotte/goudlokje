import Lean
import Lean.Elab.Frontend
import Lean.Elab.Tactic
import Lean.Elab.Import
import Lean.Meta
import Goudlokje.Analysis

open Lean Elab Meta Goudlokje

private partial def dumpTree (indent : String) (ci? : Option ContextInfo) (tree : InfoTree) : IO Unit := do
  match tree with
  | .context pci child =>
    let newCi? := pci.mergeIntoOuter? ci?
    IO.println s!"{indent}[context]"
    dumpTree (indent ++ "  ") newCi? child
  | .node info children =>
    match info with
    | .ofTacticInfo ti =>
      IO.println s!"{indent}[TacticInfo] kind={ti.stx.getKind} goalsBefore={ti.goalsBefore.length}"
    | .ofCommandInfo ci =>
      IO.println s!"{indent}[CommandInfo] elab={ci.elaborator}"
    | .ofTermInfo ti =>
      IO.println s!"{indent}[TermInfo] isType={ti.isBinder}"
    | .ofPartialTermInfo _ => IO.println s!"{indent}[PartialTermInfo]"
    | .ofMacroExpansionInfo _ => IO.println s!"{indent}[MacroExpansionInfo]"
    | .ofOptionInfo _ => IO.println s!"{indent}[OptionInfo]"
    | .ofErrorNameInfo _ => IO.println s!"{indent}[ErrorNameInfo]"
    | .ofFieldInfo _ => IO.println s!"{indent}[FieldInfo]"
    | .ofCompletionInfo _ => IO.println s!"{indent}[CompletionInfo]"
    | .ofUserWidgetInfo _ => IO.println s!"{indent}[UserWidgetInfo]"
    | .ofCustomInfo ci => IO.println s!"{indent}[CustomInfo type={ci.value.typeName}]"
    | .ofFVarAliasInfo _ => IO.println s!"{indent}[FVarAliasInfo]"
    | .ofFieldRedeclInfo _ => IO.println s!"{indent}[FieldRedeclInfo]"
    | .ofDelabTermInfo _ => IO.println s!"{indent}[DelabTermInfo]"
    | .ofChoiceInfo _ => IO.println s!"{indent}[ChoiceInfo]"
    | .ofDocInfo _ => IO.println s!"{indent}[DocInfo]"
    | .ofDocElabInfo _ => IO.println s!"{indent}[DocElabInfo]"
    for child in children do
      dumpTree (indent ++ "  ") ci? child
  | .hole id =>
    IO.println s!"{indent}[hole {id.name}] ← should not appear after substituteLazy"

def main (args : List String) : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  unsafe Lean.enableInitializersExecution
  let filePath : System.FilePath := args.headD "TestSuite/Fixtures/Simple.lean"
  let input ← IO.FS.readFile filePath
  let opts := Elab.async.set Options.empty false
  let inputCtx := Parser.mkInputContext input filePath.toString
  let (header, parserState, _messages) ← Parser.parseHeader inputCtx
  let (env, _) ← processHeader header opts {} inputCtx

  IO.println "=== Using FrontendM per-command tree collection ==="
  let initCmdState : Lean.Elab.Command.State := Lean.Elab.Command.mkState env {} opts
  let initState : Lean.Elab.Frontend.State := {
    commandState := initCmdState
    parserState  := parserState
    cmdPos       := 0
  }
  let ctx : Lean.Elab.Frontend.Context := { inputCtx }
  let mut allTrees : Array InfoTree := #[]
  let mut fstate := initState
  let mut cmdIdx := 0
  let mut keepGoing := true
  while keepGoing do
    let (isDone, newState) ← (Lean.Elab.Frontend.processCommand.run ctx).run fstate
    let cmdTrees := newState.commandState.infoState.trees.toArray
    IO.println s!"Command {cmdIdx}: {cmdTrees.size} trees"
    for i in [:cmdTrees.size] do
      IO.println s!"  Tree {i}:"
      dumpTree "    " none cmdTrees[i]!
    allTrees := allTrees ++ cmdTrees
    fstate := newState
    cmdIdx := cmdIdx + 1
    if isDone then keepGoing := false
  IO.println s!"Total accumulated trees: {allTrees.size}"

  IO.println ""
  IO.println "=== Tactic kind names ==="
  let kinds ← collectTacticKinds filePath
  for k in kinds do
    IO.println s!"  {k}"

  IO.println ""
  IO.println "=== analyzeFile results ==="
  let results ← analyzeFile filePath #["decide"]
  IO.println s!"Results: {results.size}"
  for r in results do
    IO.println s!"  {r.file}:{r.line}:{r.column} - {r.tactic}"
