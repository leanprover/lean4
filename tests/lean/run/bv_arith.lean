import Std.Tactic.BVDecide

open BitVec

theorem arith_unit_1 (x y : BitVec 64) : x + y = y + x := by
  bv_decide

theorem arith_unit_1' (x y : BitVec 64) : BitVec.add x y = y + x := by
  bv_decide

theorem arith_unit_2 (x y : BitVec 64) : x - y = -y + x := by
  bv_decide

theorem arith_unit_2' (x y : BitVec 64) : BitVec.sub x y = (BitVec.neg y) + x := by
  bv_decide

theorem arith_unit_3 (x y : BitVec 16) : x - (x - y) = y := by
  bv_decide

theorem arith_unit_4 (x y : BitVec 4) : x * y = y * x := by
  bv_decide

theorem arith_unit_5 (x : BitVec 8) : x * 32 = 32 * x := by
  bv_decide

theorem arith_unit_6 (x : BitVec 64) : x + x = 2 * x := by
  bv_decide
