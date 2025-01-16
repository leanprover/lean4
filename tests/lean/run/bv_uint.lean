import Std.Tactic.BVDecide

example (a b : UInt8) : a + b = b + a := by
  bv_decide

example (a b : UInt8) : a + b = a := by
  bv_decide
