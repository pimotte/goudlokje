-- Fixture: VerboseMultiDecl — one Verbose-style declaration followed by one plain declaration.
-- Purpose: verify that filterVerboseSteps per-step deduplication does not leak across
-- declarations; Decl 2 (no step boundaries) must keep ALL its shortcuts.
--
-- NOTE: `all_goals norm_num` at line 41 creates two TacticInfo nodes at DIFFERENT columns:
--   `all_goals`@(41,2): NOT last-position → probed → SHORTCUT (decide closes 1+1=2)
--   `norm_num`@(41,11): IS  last-position of Decl 2 → dropped by skip-last
--
-- Shortcut summary with `decide` probe:
--
--   filterVerboseSteps := false: show@29, norm_num@30, show@32 (Decl 1);
--     constructor@40, all_goals@(41,2) (Decl 2); norm_num@33 + norm_num@(41,11) → skip-last
--     Total: 5 shortcuts (lines 29, 30, 32, 40, 41)
--
--   filterVerboseSteps := true (first shortcut per step):
--     Decl 1 step 1 [show@29,norm_num@30]: show@29 → shortcut; step 2 [show@32]: shortcut
--     Decl 2 singletons: [constructor@40] → shortcut, [all_goals@(41,2)] → shortcut
--     Total: 4 shortcuts (lines 29, 32, 40, 41)
import Verbose.English.All

set_option linter.unusedTactic false

-- Decl 1 (Verbose, 2 steps):
-- Skip-last drops norm_num@33 (last tactic of Decl 1).
-- Step 1 group [show@29, norm_num@30]: probe show@29 → shortcut → stop step.
-- Step 2 group [show@32]:              probe show@32 → shortcut.
example : 1 + 1 = 2 ∧ 2 + 2 = 4 := by
  Let's first prove that 1 + 1 = 2  -- step boundary (line 28); introduces goal `1 + 1 = 2`
  show 1 + 1 = 2                    -- line 29: SHORTCUT — first tactic of step 1; `decide` closes it
  norm_num                           -- line 30: 2nd tactic in step 1; step already done → not probed
  Let's now prove that 2 + 2 = 4    -- step boundary (line 31); introduces goal `2 + 2 = 4`
  show 2 + 2 = 4                    -- line 32: SHORTCUT — only remaining tactic of step 2; `decide` closes it
  norm_num                           -- line 33: last tactic of Decl 1 → dropped by skip-last before grouping

-- Decl 2 (plain, no step boundaries): filterVerboseSteps must NOT suppress tactics here.
-- Each tactic becomes a singleton group; all shortcuts reported.
-- `all_goals norm_num` creates TWO nodes: all_goals@(41,2) probed (SHORTCUT); norm_num@(41,11) last → skip-last.
-- Singletons: [constructor@40] → SHORTCUT (decide closes full conj), [all_goals@(41,2)] → SHORTCUT.
example : 1 + 1 = 2 ∧ 2 + 2 = 4 := by
  constructor        -- line 40: SHORTCUT — `decide` closes the full conjunction goal
  all_goals norm_num -- line 41: all_goals@(41,2) → SHORTCUT; norm_num@(41,11) → last → skip-last
