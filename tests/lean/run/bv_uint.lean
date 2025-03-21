import Std.Tactic.BVDecide

/-! UInt8 -/
example (a b c : UInt8) (h1 : a < b) (h2 : b < c) : a < c := by
  bv_decide

/--
error: The prover found a counterexample, consider the following assignment:
a = 255
b = 255
-/
#guard_msgs in
example (a b : UInt8) : a + b > a := by
  bv_decide



/-! UInt16 -/
example (a b c : UInt16) (h1 : a < b) (h2 : b < c) : a < c := by
  bv_decide

/--
error: The prover found a counterexample, consider the following assignment:
a = 65535
b = 65535
-/
#guard_msgs in
example (a b : UInt16) : a + b > a := by
  bv_decide



/-! UInt32 -/
example (a b c : UInt32) (h1 : a < b) (h2 : b < c) : a < c := by
  bv_decide

/--
error: The prover found a counterexample, consider the following assignment:
a = 4294967295
b = 4294967295
-/
#guard_msgs in
example (a b : UInt32) : a + b > a := by
  bv_decide



/-! UInt64 -/
example (a b c : UInt64) (h1 : a < b) (h2 : b < c) : a < c := by
  bv_decide

/--
error: The prover found a counterexample, consider the following assignment:
a = 18446744073709551615
b = 18446744073709551615
-/
#guard_msgs in
example (a b : UInt64) : a + b > a := by
  bv_decide



/-! USize -/
example (a b c : USize) (h1 : a < b) (h2 : b < c) : a < c := by
  cases System.Platform.numBits_eq <;> bv_decide

/--
warning: Detected USize/ISize in the goal but no hypothesis about System.Platform.numBits, consider case splitting on System.Platform.numBits_eq
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example (a b : USize) : a + b > a := by
  bv_normalize
  sorry

example (h : 32 = System.Platform.numBits) (a b c : USize) (h1 : a < b) (h2 : b < c) : a < c := by
  bv_decide
