import Std.Tactic.BVDecide


/--
error: The prover found a counterexample, consider the following assignment:
x = 0#32
y = 2147483648#32
-/
#guard_msgs in
example (x y : BitVec 32) : x * y = y + x := by
  bv_decide

/--
error: The prover found a counterexample, consider the following assignment:
x = 0#32
y = 2147483648#32
-/
#guard_msgs in
example (x y : BitVec 32) : x * y = y + x := by
  bv_decide (config := { solverMode := .counterexample })

/--
error: The prover found a counterexample, consider the following assignment:
x = 0#32
y = 2147483648#32
-/
#guard_msgs in
example (x y : BitVec 32) : x * y = y + x := by
  bv_decide (config := { solverMode := .default })

/--
error: The prover found a counterexample, consider the following assignment:
x = 0#32
y = 2147483648#32
-/
#guard_msgs in
example (x y : BitVec 32) : x * y = y + x := by
  bv_decide (config := { solverMode := .proof })
