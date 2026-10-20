module
import Std.Tactic.BVDecide

example (c : UInt16) (l : UInt8) : ((c, l).2).toUInt32 = l.toUInt32 := by
  bv_decide
