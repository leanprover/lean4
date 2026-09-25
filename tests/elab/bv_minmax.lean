module
import Std.Tactic.BVDecide
meta import Std.Tactic.BVDecide

/-! Test the min/max integration of bv_decide -/

example (a b : BitVec 64) : min a b = min b a := by
  bv_decide

example (a b : UInt8) : min a b = min b a := by
  bv_decide

example (a b : UInt16) : min a b = min b a := by
  bv_decide

example (a b : UInt32) : min a b = min b a := by
  bv_decide

example (a b : UInt64) : min a b = min b a := by
  bv_decide

example (a b : USize) : min a b = min b a := by
  cases System.Platform.numBits_eq <;> bv_decide

example (a b : Int8) : min a b = min b a := by
  bv_decide

example (a b : Int16) : min a b = min b a := by
  bv_decide

example (a b : Int32) : min a b = min b a := by
  bv_decide

example (a b : Int64) : min a b = min b a := by
  bv_decide

example (a b : ISize) : min a b = min b a := by
  cases System.Platform.numBits_eq <;> bv_decide

example (a b : BitVec 64) : max a b = max b a := by
  bv_decide

example (a b : UInt8) : max a b = max b a := by
  bv_decide

example (a b : UInt16) : max a b = max b a := by
  bv_decide

example (a b : UInt32) : max a b = max b a := by
  bv_decide

example (a b : UInt64) : max a b = max b a := by
  bv_decide

example (a b : USize) : max a b = max b a := by
  cases System.Platform.numBits_eq <;> bv_decide

example (a b : Int8) : max a b = max b a := by
  bv_decide

example (a b : Int16) : max a b = max b a := by
  bv_decide

example (a b : Int32) : max a b = max b a := by
  bv_decide

example (a b : Int64) : max a b = max b a := by
  bv_decide

example (a b : ISize) : max a b = max b a := by
  cases System.Platform.numBits_eq <;> bv_decide
