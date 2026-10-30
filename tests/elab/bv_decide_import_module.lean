module
import Std.Tactic.BVDecide

theorem foo {x y : BitVec 64} : x ^^^ y ^^^ x ^^^ y = 0 := by
  bv_decide
