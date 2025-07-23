import Std.Tactic.BVDecide

-- This previously was an internal error due to the constant shift not being eliminated because
-- of the non constant width shift, now it's an error.

/--
error: The prover found a potentially spurious counterexample:
- It abstracted the following unsupported expressions as opaque variables: [x <<< 1 == x]
Consider the following assignment:
x <<< 1 == x = false
-/
#guard_msgs in
example (x : BitVec w) : x <<< (1 : Nat) = x := by
  bv_decide
