import Std.Tactic.BVDecide

set_option trustCompiler true

theorem bitvec_InstCombineShift__351 :
    ∀ (X C1 C2 : BitVec 10), (X * C1) <<< C2 = X * (C1 <<< C2) := by
  intros
  bv_decide
