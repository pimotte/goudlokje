-- Fixture for testing Lean Verbose step filtering.
-- Each step has two tactics: `show` (a no-op) followed by `norm_num`.
-- `decide` is a shortcut at BOTH positions within each step body.
--
-- With filterVerboseSteps = false: 4 shortcuts total (2 per step, at `show` and `norm_num`).
--   skip-last drops norm_num@16 (last tactic overall); `decide` still fires at show@12,
--   norm_num@13, show@15 (3 positions), plus norm_num@16 is skipped → actually 3 shortcuts.
--   Wait: skip-last drops norm_num@16; so 4 tactic positions minus 1 = 3 probed; all succeed.
--
-- With filterVerboseSteps = true:  2 shortcuts total (1 per step, at the `show` tactic each).
--   skip-last is applied first (to non-boundary tactics): drops norm_num@16 (last overall).
--   Step 1 group [show@12, norm_num@13]: probe show@12 → shortcut → stop; 1 shortcut.
--   Step 2 group [show@15]:              probe show@15 → shortcut; 1 shortcut.
--   norm_num@13 is in the group but not probed (step 1 already done).
--   norm_num@16 is dropped by skip-last before grouping.
import Verbose.English.All

set_option linter.unusedTactic false

example : 1 + 1 = 2 ∧ 2 + 2 = 4 := by
  Let's first prove that 1 + 1 = 2
  show 1 + 1 = 2   -- line 12: SHORTCUT (step 1 first tactic); decide closes; stops step
  norm_num          -- line 13: in step 1 group but not probed (step 1 already done)
  Let's now prove that 2 + 2 = 4
  show 2 + 2 = 4   -- line 15: SHORTCUT (step 2 first tactic); decide closes; not last
  norm_num          -- line 16: last tactic overall → dropped by skip-last before grouping
