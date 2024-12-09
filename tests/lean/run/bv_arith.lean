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

theorem arith_unit_5 (x : BitVec 64) : x * 32 = 32 * x := by
  bv_decide

theorem arith_unit_6 (x : BitVec 64) : x + x = 2 * x := by
  bv_decide

theorem arith_unit_7 (x : BitVec 16) : x / 1 = x := by
  bv_decide

theorem arith_unit_8 (x y : BitVec 16) : x / y ≤ x := by
  bv_decide

theorem arith_unit_8' (x y : BitVec 16) : x.udiv y ≤ x := by
  bv_decide

theorem arith_unit_9 (x : BitVec 16) : x % 1 = 0 := by
  bv_decide

theorem arith_unit_10 (x y : BitVec 8) : x % y ≤ x := by
  bv_decide

theorem arith_unit_10' (x y : BitVec 8) : x.umod y ≤ x := by
  bv_decide

theorem arith_unit_11 (x y : BitVec 8) (hx : x.msb = false) (hy : y.msb = false) : x / y = x.sdiv y := by
  bv_decide

theorem arith_unit_12 (x y : BitVec 8) (hx : x.msb = false) (hy : y.msb = true) : -(x / -y) = x.sdiv y := by
  bv_decide

theorem arith_unit_13 (x y : BitVec 8) (hx : x.msb = false) (hy : y.msb = false) : x.umod y = x.smod y := by
  bv_decide

theorem arith_unit_14 (x y : BitVec 8) (hx : x.msb = true) (hy : y.msb = true) : (-((-x).umod (-y))) = x.smod y := by
  bv_decide

theorem arith_unit_15 (x : BitVec 32) : BitVec.sle x (BitVec.abs x) := by
  bv_decide

theorem arith_unit_16 (x y : BitVec 8)  (hy : y ≠ 0) : x.smtUDiv y = x / y := by
  bv_decide

theorem arith_unit_17 (x y : BitVec 8)  (hy : y = 0) : x.smtUDiv y = -1#8 := by
  bv_decide

theorem arith_unit_18 (x y : BitVec 8)  (hx : x.msb = true) (h : y.msb = true) : x.smtSDiv y = (-x).smtUDiv (-y) := by
  bv_decide

theorem arith_unit_19 (x y : BitVec 8)  (hx : x.msb = true) (h : y.msb = true) : x.srem y = -((-x) % (-y)) := by
  bv_decide
