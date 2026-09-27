import Goudlokje.Scope

/-! Tests for finding student input areas. -/

open Goudlokje

#guard inputAreas "no markers\nat all" == #[]

#guard inputAreas "a\n:::input\nb\nc\n:::\nd" == #[{ first := 3, last := 4 }]

-- Several areas; an area still open at the end of the file extends to the last line.
#guard inputAreas ":::input\nx\n:::\ny\n:::input\nz\nw" ==
  #[{ first := 2, last := 2 }, { first := 6, last := 7 }]

-- Markers inside a Lean fence are student code, not area markers.
#guard inputAreas ":::input\n```lean\n:::\n```\n:::" == #[{ first := 2, last := 4 }]

-- A closing marker without an opening one is ignored.
#guard inputAreas ":::\na" == #[]
