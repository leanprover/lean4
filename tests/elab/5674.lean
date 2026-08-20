import Std.Tactic.BVDecide

/--
error: The prover found a potentially spurious counterexample:
- The following potentially relevant hypotheses could not be used:
  - 0 < b.toNat derived via assumption h
Consider the following assignment:
b = 0#64
-/
#guard_msgs in
example
    (b : BitVec 64)
    (h : b.toNat > 0) :
    b > 0 := by
  bv_decide
