/-!
Regression tests for #15108: the goal view must show the goal of an empty `grind =>`, `sym =>` and
`impossible by` block, both right after the token and on the following indented line where the next
tactic is about to be typed. The goal used to be admitted inside the innermost `TacticInfo` node,
so its after-state was empty.
-/

example : False := by
  grind =>
        --^ $/lean/plainGoal
    -- cursor here
  --^ $/lean/plainGoal

example : False := by
  sym =>
      --^ $/lean/plainGoal
    -- cursor here
  --^ $/lean/plainGoal

example : False := by
  impossible by
             --^ $/lean/plainGoal
    -- cursor here
  --^ $/lean/plainGoal

-- Non-empty sequences are unaffected: the state after the last tactic is shown.
example : False := by
  grind =>
    skip
    -- cursor here
  --^ $/lean/plainGoal

example : False := by
  impossible by
    skip
    -- cursor here
  --^ $/lean/plainGoal

-- As for `case x =>`, the tactic head shows the start state of the nested block.
example : False := by
  grind =>
--^ $/lean/plainGoal
    skip
