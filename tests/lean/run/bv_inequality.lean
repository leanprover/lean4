import Std.Tactic.BVDecide

open BitVec

theorem ineq_unit_1 (x y : BitVec 64) (h : x ≠ y) : y ≠ x := by
  bv_decide

theorem ineq_unit_2 (x y z : BitVec 32) (h1 : x < y) (h2 : y < z)  : x < z := by
  bv_decide

theorem ineq_unit_2' (x y z : BitVec 32) (h1 : BitVec.ult x y) (h2 : y < z)  : BitVec.ult x z := by
  bv_decide

theorem ineq_unit_3 (x y z : BitVec 32) (h1 : x ≤ y) (h2 : y ≤ z)  : x ≤ z := by
  bv_decide

theorem ineq_unit_3' (x y z : BitVec 32) (h1 : BitVec.ule x y) (h2 : y ≤ z)  : BitVec.ule x z := by
  bv_decide

theorem ineq_unit_4 (x y z : BitVec 32) (h1 : x > y) (h2 : y > z)  : x > z := by
  bv_decide

theorem ineq_unit_5 (x y z : BitVec 32) (h1 : x ≥ y) (h2 : y ≥ z)  : x ≥ z := by
  bv_decide

theorem ineq_unit_6 (x y z : BitVec 32) (h1 : BitVec.slt x y) (h2 : BitVec.slt y z)  : BitVec.slt x z := by
  bv_decide

theorem ineq_unit_7 (x y z : BitVec 32) (h1 : BitVec.sle x y) (h2 : BitVec.sle y z)  : BitVec.sle x z := by
  bv_decide
