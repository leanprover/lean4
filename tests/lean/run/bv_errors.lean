import Std.Tactic.BVDecide

open BitVec

/--
error: The SAT solver timed out while solving the problem.
Consider increasing the timeout with the `timeout` config option.
If solving your problem relies inherently on using associativity or commutativity, consider enabling the `acNf` config option.
-/
#guard_msgs in
theorem timeout (x y z : BitVec 1024) : x - (y + z) = x - y - z := by
  bv_decide (config := { timeout := 1 })

/--
error: None of the hypotheses are in the supported BitVec fragment.
There are two potential fixes for this:
1. If you are using custom BitVec constructs simplify them to built-in ones.
2. If your problem is using only built-in ones it might currently be out of reach.
   Consider expressing it in terms of different operations that are better supported.
-/
#guard_msgs in
theorem no_hyps (x y : Nat) : x * y = y * x := by
  bv_decide
