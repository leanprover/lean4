import Std.Tactic.BVDecide

open BitVec

set_option exponentiation.threshold 4096

theorem t1 {x y : BitVec 64} (h : x = y) : (~~~x) &&& y = (~~~y) &&& x := by
  bv_decide

theorem t2 {x y : BitVec 512} (h : x = y) : (~~~x) &&& y = (~~~y) &&& x := by
  bv_decide

theorem t3 {x y : BitVec 1024} (h : x = y) : (~~~x) &&& y = (~~~y) &&& x := by
  bv_decide

theorem t4 {x y : BitVec 2048} (h : x = y) : (~~~x) &&& y = (~~~y) &&& x := by
  bv_decide

theorem t5 {x y : BitVec 4096} (h : x = y) : (~~~x) &&& y = (~~~y) &&& x := by
  bv_decide
