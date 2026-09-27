import Goudlokje.Report

/-! Tests for the results-file format. -/

open Goudlokje Lean

private def finding : Finding := {
  check := .shortcut, exercise := "1.1.13", step := 2, line := 20, column := 2
  tactic? := some "decide", message := "…" }

#guard (toJson (ResultRecord.exercise "1.1.13" #["sorry"])).compress ==
  "{\"checks\":[\"sorry\"],\"exercise\":\"1.1.13\"}"

#guard (fromJson? (toJson (ResultRecord.finding finding))).toOption == some (ResultRecord.finding finding)
#guard (fromJson? (toJson (ResultRecord.exercise "a" #["shortcut"]))).toOption ==
  some (ResultRecord.exercise "a" #["shortcut"])
#guard (fromJson? (toJson (ResultRecord.skipped "a"))).toOption == some (ResultRecord.skipped "a")
#guard (fromJson? (toJson (ResultRecord.header 1 0xFFFFFFFFFFFFFFFF))).toOption ==
  some (ResultRecord.header 1 0xFFFFFFFFFFFFFFFF)

-- Checks are written by name.
#guard ((toJson finding).getObjValD "check") == "shortcut"
