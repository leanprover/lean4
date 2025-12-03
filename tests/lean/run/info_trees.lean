-- This tests the `#info_trees in` command.
-- If it proves too fragile to test the result using `#guard_msgs`,
-- it is fine to simply remove the `#guard_msgs` and expected output.

#guard_msgs (drop info) in
#info_trees in
theorem t (n : Nat) : 0 ≤ n := by exact?
