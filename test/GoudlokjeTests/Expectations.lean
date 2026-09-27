import Goudlokje.Expectations

/-! Tests for reading and writing `.test.json` files. -/

open Goudlokje Lean

private def sample : Expectations := {
  exercises := ({} : Std.TreeMap String ExerciseExpectations compare)
    |>.insert "1.1.13" { shortcuts := #[{ step := 1, tactic := "decide" }], allowSorry := true }
    |>.insert "b" { lint := #[{ check := "typeAscription", step := 3 }] }
}

-- Round trip.
#guard match parseExpectations (toJson sample).compress with
  | .ok e => e.exercises.toList == sample.exercises.toList
  | .error _ => false

-- Absent fields take their defaults; unknown exercises have no expectations.
#guard match parseExpectations "{\"testJsonVersion\": 3, \"exercises\": {\"a\": {}}}" with
  | .ok e => e.get "a" == {} && e.get "missing" == {}
  | .error _ => false

-- Files without the current version are rejected, so old files are regenerated.
#guard (parseExpectations "{\"expected\": []}").isOk == false
#guard (parseExpectations "{\"testJsonVersion\": 2, \"exercises\": {}}").isOk == false

-- Empty fields are omitted when writing.
#guard (toJson ({ exercises := ({} : Std.TreeMap _ _ compare).insert "a" {} } : Expectations)).compress ==
  "{\"exercises\":{\"a\":{}},\"testJsonVersion\":3}"

-- Files are written with sorted keys, one per line.
#guard renderJson (toJson sample) == "{
  \"exercises\": {
    \"1.1.13\": {
      \"allowSorry\": true,
      \"shortcuts\": [
        {\"step\":1,\"tactic\":\"decide\"}
      ]
    },
    \"b\": {
      \"lint\": [
        {\"check\":\"typeAscription\",\"step\":3}
      ]
    }
  },
  \"testJsonVersion\": 3
}"

-- Which issues are expected; raw tactics never are.
private def ex : ExerciseExpectations := {
  shortcuts := #[{ step := 1, tactic := "decide" }]
  lint := #[{ check := "typeAscription", step := 3 }, { check := "rawTactic", step := 4 }] }

#guard ex.expects .shortcut 1 "decide" && !ex.expects .shortcut 1 "simp" && !ex.expects .shortcut 2 "decide"
#guard ex.expects .typeAscription 3 && !ex.expects .typeAscription 4
#guard !ex.expects .rawTactic 4
#guard !ex.expects .sorry 1 && ({ allowSorry := true } : ExerciseExpectations).expects .sorry 7

-- Stale entries: only for checks that ran; invalid entries (raw tactics, unknown checks) always.
#guard ex.stale #[] #[] == #[.lint { check := "rawTactic", step := 4 } true]
#guard ex.stale Check.all #[(.shortcut, 1, some "decide"), (.typeAscription, 3, none)] ==
  #[.lint { check := "rawTactic", step := 4 } true]
#guard ex.stale Check.all #[] ==
  #[.shortcut { step := 1, tactic := "decide" }, .lint { check := "typeAscription", step := 3 } false,
    .lint { check := "rawTactic", step := 4 } true]
#guard ({ allowSorry := true } : ExerciseExpectations).stale #[.sorry] #[] == #[.allowSorry]
#guard ({ allowSorry := true } : ExerciseExpectations).stale #[.sorry] #[(.sorry, 2, none)] == #[]
#guard ({ lint := #[{ check := "x", step := 1 }] } : ExerciseExpectations).stale #[] #[] ==
  #[.lint { check := "x", step := 1 } true]
