import Std.Tactic.BVDecide

open BitVec

theorem substructure_unit_1 (x y z : BitVec 8) : ((x = y) ∧ (y = z)) ↔ ¬(¬(x =y) ∨ (¬(y = z))) := by
  bv_decide

theorem substructure_unit_1' (x y z : BitVec 8) : ((x = y) && (y = z)) ↔ ¬(¬(x = y) || (!(y = z))) := by
  bv_decide

theorem substructure_unit_1'' (x y z : BitVec 8) : (Bool.and (x = y) (y = z)) ↔ ¬(Bool.or (!(x = y)) (Bool.not (y = z))) := by
  bv_decide

theorem substructure_unit_2 (x y : BitVec 8) : x = y → y = x := by
  bv_decide

theorem substructure_unit_3 (x y : BitVec 8) : (x = y) ^^ (y ≠ x) := by
  bv_decide

theorem substructure_unit_3' (x y : BitVec 8) : Bool.xor (x = y) (y ≠ x) := by
  bv_decide

theorem substructure_unit_4 (a b : Bool) : (a && b) = (b && a) := by
  bv_decide

theorem substructure_unit_5 (a : Bool) (b c : BitVec 32) (h1 : b < c ↔ a) (h2 : a = true) : b < c := by
  bv_decide

theorem substructure_unit_6 (a b c: Bool) : (if a then b else c) = (if !a then c else b) := by
  bv_decide

theorem substructure_unit_7 (a b c: Bool) : (bif a then b else c) = (bif !a then c else b) := by
  bv_decide

theorem substructure_unit_8 (x : BitVec 32) : (if x.getLsbD 0 then !x.getLsbD 0 else x.getLsbD 0) = false := by
  bv_decide

theorem substructure_unit_9 (x y : BitVec 32) (h : x.getLsbD 0 = false) : (if x.getLsbD 0 then x else y) = y := by
  bv_decide
