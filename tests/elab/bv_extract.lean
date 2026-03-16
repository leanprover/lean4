import Std.Tactic.BVDecide

open BitVec

theorem bv_extract_1 (h : x = 1#64) : extractLsb' 32 32 x = 0#32 := by
  bv_decide

theorem bv_extract_2 (h : x = 1#64) : extractLsb' 0 32 x = 1#32 := by
  bv_decide

theorem bv_extract_3 (h : x = 1#64) : extractLsb 63 32 x = 0#32 := by
  bv_decide

theorem bv_extract_4 (h : x = 1#64) : extractLsb 31 0 x = 1#32 := by
  bv_decide

theorem bv_ofBool_1 (h : x = 1#64) : ofBool (x.getLsbD 0) = 1#1 := by
  bv_decide

theorem bv_ofBool_2 (h : x = 1#64) : ofBool (x.getLsbD 1) = 0#1 := by
  bv_decide

theorem bv_ofBool_3 (h : x = 1#64) : ofBool x[0] = 1#1 := by
  bv_decide

theorem bv_ofBool_4 (h : x = 1#64) : ofBool x[1] = 0#1 := by
  bv_decide
