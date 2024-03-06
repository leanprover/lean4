-- `simp_arith` does not support `Int` yet.
-- But, the weird error message at #2615 is not generated anymore
/--
error: simp made no progress
-/
#guard_msgs (error) in
theorem huh (x : Int) : x + 1 = 1 + x := by simp_arith
