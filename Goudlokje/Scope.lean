import Lean.Elab.Command
import Goudlokje.FileCache

/-!
# Scope

Decides which parts of a worksheet Goudlokje checks: only student input areas, i.e. the lines
between a `:::input` and its closing `:::` in a Waterproof `#doc` file. Files without input areas
are not checked at all.

The markers live in the document text, not in the Lean code that the linters see, so the areas are
computed from the file on disk, once per file (and again when it is saved). The source text of the
command cannot be used instead: the Waterproof genre elaborates a copy of the document in which
everything but the Lean code is blanked out, and input areas are replaced by the same placeholder
as other prose. As a consequence, while a worksheet is edited, the areas are those of the saved
file.
-/

namespace Goudlokje

open Lean Elab Command

/-- A range of source lines (1-based, inclusive). -/
structure LineRange where
  first : Nat
  last  : Nat
  deriving Repr, BEq, Inhabited

/-- Whether `line` lies in `r`. -/
def LineRange.contains (r : LineRange) (line : Nat) : Bool :=
  r.first ≤ line && line ≤ r.last

/-- The student input areas of a file: the lines strictly between `:::input` and the matching
    `:::`. Markers inside a ```` ```lean ```` fence are student code and are ignored. An area that is
    still open at the end of the file extends to the last line. -/
def inputAreas (source : String) : Array LineRange := Id.run do
  let lines := source.splitOn "\n"
  let mut areas := #[]
  let mut inFence := false
  let mut areaStart : Option Nat := none
  let mut lineNo := 0
  for line in lines do
    lineNo := lineNo + 1
    let trimmed := line.trimAscii
    if inFence then
      if trimmed == "```" then inFence := false
    else if trimmed.startsWith "```lean" then
      inFence := true
    else if trimmed == ":::input" then
      areaStart := some (lineNo + 1)
    else if trimmed == ":::" then
      if let some first := areaStart then
        areas := areas.push { first, last := lineNo - 1 }
      areaStart := none
  if let some first := areaStart then
    areas := areas.push { first, last := lines.length }
  return areas

private initialize inputAreaCache : FileCache (Array LineRange) ← IO.mkRef {}

/-- The input areas of the file being elaborated, as saved on disk (empty if it cannot be read). -/
def getInputAreas : CommandElabM (Array LineRange) := do
  let path : System.FilePath := ← getFileName
  inputAreaCache.get path do
    try pure (inputAreas (← IO.FS.readFile path)) catch _ => pure #[]

/-- Whether `line` of the current file lies in a student input area. -/
def inInputArea (line : Nat) : CommandElabM Bool :=
  return (← getInputAreas).any (·.contains line)

end Goudlokje
