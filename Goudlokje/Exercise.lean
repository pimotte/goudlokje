import Goudlokje.Steps
import Goudlokje.Scope
import Goudlokje.Expectations

/-!
# Exercises

The unit Goudlokje checks: one command (a Verbose `Exercise`, an `example`, a theorem, …) together
with everything the checks need about it, computed once per command.
-/

namespace Goudlokje

open Lean Elab Command

/-- A command that Goudlokje checks. -/
structure Exercise where
  /-- The command. -/
  stx          : Syntax
  /-- The name identifying the exercise in `.test.json` (see `exerciseName`). -/
  name         : String
  /-- The proof steps, in source order; step numbers are positions in it. -/
  steps        : Array Step
  fileMap      : FileMap
  /-- The modules whose tactics count as Verbose (see `verboseModules`). -/
  verbose      : Array Name
  /-- The student input areas of the file. -/
  inputAreas   : Array LineRange
  /-- What `.test.json` expects in this exercise. -/
  expectations : ExerciseExpectations

namespace Exercise

/-- The number of step `s` in the exercise, as used in `.test.json`. -/
def stepNumber (e : Exercise) (s : Step) : Nat :=
  Goudlokje.stepNumber e.steps s

/-- Whether step `s` is written with a Lean Verbose tactic. -/
def isVerbose (e : Exercise) (env : Environment) (s : Step) : Bool :=
  s.isVerbose env e.verbose

/-- Whether step `s` lies in a student input area. -/
def inInputArea (e : Exercise) (s : Step) : Bool :=
  e.inputAreas.any (·.contains (s.line e.fileMap))

/-- The steps in student input areas: the steps that are checked. -/
def inputSteps (e : Exercise) : Array Step :=
  e.steps.filter e.inInputArea

end Exercise

/-- The exercise declared by the command `stx`, if Goudlokje checks it: it is written with Lean
    Verbose (a Verbose command, or a proof using Verbose tactics), and some of its steps lie in a
    student input area. An unreadable `.test.json` is reported as an error. The caller checks that
    the command elaborated without errors. -/
def getExercise? (stx : Syntax) : CommandElabM (Option Exercise) := do
  let steps := collectSteps stx (← getInfoTrees)
  if steps.isEmpty then return none
  let env ← getEnv
  let verbose := verboseModules (← getOptions)
  unless isVerboseKind env verbose stx.getKind || steps.any (·.isVerbose env verbose) do
    return none
  let fileMap ← getFileMap
  let inputAreas ← getInputAreas
  unless steps.any (fun s => inputAreas.any (·.contains (s.line fileMap))) do return none
  let name := exerciseName env verbose stx
  let expectations ← match ← getExpectations with
    | .ok expectations => pure (expectations.get name)
    | .error msg => logErrorAt stx msg; return none
  return some { stx, name, steps, fileMap, verbose, inputAreas, expectations }

end Goudlokje
