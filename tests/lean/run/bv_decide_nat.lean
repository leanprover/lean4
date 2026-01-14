import Std.Tactic.BVDecide

theorem cex (n : Nat) (hn : BitVec.ofNat 64 n ≠ 0) : BitVec.ofNat 64 n ≠ 0#64 := by
  bv_decide
