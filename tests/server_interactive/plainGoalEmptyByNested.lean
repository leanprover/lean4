/-!
Regression tests for #15053 (and #1927): after an empty nested `have ... := by`, positions that
are indented past the `have` must show the goal of the empty block, not the state after `have`.
The `by` block's own column must not count as indentation.
-/

-- Issue example 2: expected `⊢ True` right after `by` (col 19) and on the next line at cols 5 and
-- 3; the outer state is shown at col 0 (and at col 2, the `have` column).
example : False := by
  have : True := by
                 --^ $/lean/plainGoal
    -- cursor here
   --^ $/lean/plainGoal
 --^ $/lean/plainGoal
--⬑ $/lean/plainGoal

-- Same, but with a completely empty line and a following outer tactic
example : False := by
  have : True := by

  --^ $/lean/plainGoal
  sorry

example : False := by
  have : True := by
    -- cursor here
   --^ $/lean/plainGoal
 --^ $/lean/plainGoal
  sorry

-- Control: empty top-level `by` at EOF (`plainGoalEmptyBy.lean` covers more of these)
example : False := by
  -- cursor here
 --^ $/lean/plainGoal
