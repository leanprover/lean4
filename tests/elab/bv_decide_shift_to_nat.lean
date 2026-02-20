import Std.Tactic.BVDecide

theorem test2 (b s : BitVec 5) (hb : b = 0) (hs : s ≠ 0) :
    b <<< s.toNat = 0 := by
  bv_decide

theorem test2' (b s : BitVec 5) (hb : b = 0) (hs : s ≠ 0) :
    b >>> s.toNat = 0 := by
  bv_decide

theorem test2'' (b s : BitVec 5) (hb : b = 0) (hs : s ≠ 0) :
    BitVec.sshiftRight b s.toNat = 0 := by
  bv_decide

theorem test2''' (b s : BitVec 5) (hb : b = 0) (hs : s ≠ 0) :
    BitVec.shiftLeft b s.toNat = 0 := by
  bv_decide

theorem test2'''' (b s : BitVec 5) (hb : b = 0) (hs : s ≠ 0) :
    BitVec.ushiftRight b s.toNat = 0 := by
  bv_decide
