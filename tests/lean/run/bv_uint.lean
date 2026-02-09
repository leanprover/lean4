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
warning: declaration uses `sorry`
-/
#guard_msgs in
example (a b : USize) : a + b > a := by
  bv_normalize
  sorry

example (h : 32 = System.Platform.numBits) (a b c : USize) (h1 : a < b) (h2 : b < c) : a < c := by
  bv_decide

example (n : UInt8) : n.toInt8.toUInt8 = n := by bv_decide
example (n : UInt16) : n.toInt16.toUInt16 = n := by bv_decide
example (n : UInt32) : n.toInt32.toUInt32 = n := by bv_decide
example (n : UInt64) : n.toInt64.toUInt64 = n := by bv_decide

example (n : Int8) : n.toUInt8.toInt8 = n := by bv_decide
example (n : Int16) : n.toUInt16.toInt16 = n := by bv_decide
example (n : Int32) : n.toUInt32.toInt32 = n := by bv_decide
example (n : Int64) : n.toUInt64.toInt64 = n := by bv_decide

example {b : UInt8} (h : b &&& 0x80 == 0) : b < 0x80 := by bv_decide

example (x y z: UInt8) (h1 : x == y) (h2 : y == z) : x == z := by bv_decide
example (x y z: UInt16) (h1 : x == y) (h2 : y == z) : x == z := by bv_decide
example (x y z: UInt32) (h1 : x == y) (h2 : y == z) : x == z := by bv_decide
example (x y z: UInt64) (h1 : x == y) (h2 : y == z) : x == z := by bv_decide

example (x y z: Int8) (h1 : x == y) (h2 : y == z) : x == z := by bv_decide
example (x y z: Int16) (h1 : x == y) (h2 : y == z) : x == z := by bv_decide
example (x y z: Int32) (h1 : x == y) (h2 : y == z) : x == z := by bv_decide
example (x y z: Int64) (h1 : x == y) (h2 : y == z) : x == z := by bv_decide
