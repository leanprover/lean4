import Std.Tactic.BVDecide

open BitVec

theorem bv_extract_1 : extractLsb' 32 32 (1#64) = 0#32 := by
  bv_decide

theorem bv_extract_2 : extractLsb' 0 32 (1#64) = 1#32 := by
  bv_decide

theorem bv_extract_3 : extractLsb 63 32 (1#64) = 0#32 := by
  bv_decide

theorem bv_extract_4 : extractLsb 31 0 (1#64) = 1#32 := by
  bv_decide
