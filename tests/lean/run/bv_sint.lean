import Std.Tactic.BVDecide

/-! Int8 -/
example (a b c : Int8) (h1 : a < b) (h2 : b < c) : a < c := by
  bv_decide

/--
error: The prover found a counterexample, consider the following assignment:
a = -1
b = -1
-/
#guard_msgs in
example (a b : Int8) : a + b > a := by
  bv_decide



/-! Int16 -/
example (a b c : Int16) (h1 : a < b) (h2 : b < c) : a < c := by
  bv_decide

/--
error: The prover found a counterexample, consider the following assignment:
a = -1
b = -1
-/
#guard_msgs in
example (a b : Int16) : a + b > a := by
  bv_decide



/-! Int32 -/
example (a b c : Int32) (h1 : a < b) (h2 : b < c) : a < c := by
  bv_decide

/--
error: The prover found a counterexample, consider the following assignment:
a = -1
b = -1
-/
#guard_msgs in
example (a b : Int32) : a + b > a := by
  bv_decide



/-! Int64 -/
example (a b c : Int64) (h1 : a < b) (h2 : b < c) : a < c := by
  bv_decide

/--
error: The prover found a counterexample, consider the following assignment:
a = -1
b = -1
-/
#guard_msgs in
example (a b : Int64) : a + b > a := by
  bv_decide



/-! ISize -/
example (a b c : ISize) (h1 : a < b) (h2 : b < c) : a < c := by
  cases System.Platform.numBits_eq <;> bv_decide

/--
warning: Detected USize/ISize in the goal but no hypothesis about System.Platform.numBits, consider case splitting on System.Platform.numBits_eq
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example (a b : ISize) : a + b > a := by
  bv_normalize
  sorry

example (h : 32 = System.Platform.numBits) (a b c : ISize) (h1 : a < b) (h2 : b < c) : a < c := by
  bv_decide
