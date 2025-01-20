import Std.Tactic.BVDecide

/-! UInt8 -/
example (a b : UInt8) : a + b = b + a := by
  bv_decide

/--
error: The prover found a counterexample, consider the following assignment:
a.toBitVec = 0xff#8
b.toBitVec = 0xff#8
-/
#guard_msgs in
example (a b : UInt8) : a + b = a := by
  bv_decide



/-! UInt16 -/
example (a b : UInt16) : a + b = b + a := by
  bv_decide

/--
error: The prover found a counterexample, consider the following assignment:
a.toBitVec = 0xffff#16
b.toBitVec = 0xffff#16
-/
#guard_msgs in
example (a b : UInt16) : a + b = a := by
  bv_decide



/-! UInt32 -/
example (a b : UInt32) : a + b = b + a := by
  bv_decide

/--
error: The prover found a counterexample, consider the following assignment:
a.toBitVec = 0xffffffff#32
b.toBitVec = 0xffffffff#32
-/
#guard_msgs in
example (a b : UInt32) : a + b = a := by
  bv_decide



/-! UInt64 -/
example (a b : UInt64) : a + b = b + a := by
  bv_decide

/--
error: The prover found a counterexample, consider the following assignment:
a.toBitVec = 0xffffffffffffffff#64
b.toBitVec = 0xffffffffffffffff#64
-/
#guard_msgs in
example (a b : UInt64) : a + b = a := by
  bv_decide





/-! USize -/
example (a b : USize) : a + b = b + a := by
  rcases System.Platform.numBits_eq with h | h
  · simp only [int_toBitVec]
    subst h
    simp only [h, int_toBitVec]
    bv_decide
    sorry
  · sorry
  bv_decide

/--
error: The prover found a counterexample, consider the following assignment:
a.toBitVec = 0xff#8
b.toBitVec = 0xff#8
-/
#guard_msgs in
example (a b : USize) : a + b = a := by
  bv_decide
