import Goudlokje.Check
import Goudlokje.Steps

/-!
# Issues

The issues the checks find in an exercise.
-/

namespace Goudlokje

open Lean

/-- An issue found by a check. -/
structure Issue where
  check    : Check
  /-- The step the issue is in. -/
  step     : Step
  /-- The syntax to report the issue at (the step or part of it). -/
  ref      : Syntax
  /-- For shortcuts: the probe tactic that closes the goal. -/
  tactic?  : Option String := none
  message  : MessageData

end Goudlokje
