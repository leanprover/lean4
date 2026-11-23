module
import Std.Tactic.BVDecide

set_option trustCompiler true

theorem foo {x y : BitVec 64} : x ^^^ y ^^^ x ^^^ y = 0 := by
  bv_decide
