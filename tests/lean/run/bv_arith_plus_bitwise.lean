import Std.Tactic.BVDecide

open BitVec

set_option trace.Meta.Tactic.bv true

theorem add_eq_sub_not_sub_one (x y : BitVec 32):
    x + y = x - ~~~ y - 1 := by
  bv_decide -- this one hangs with ac_nf enabled

set_option bv.ac_nf false in
theorem add_eq_sub_not_sub_one' (x y : BitVec 32):
    x + y = x - ~~~ y - 1 := by
  bv_normalize
  rename_i a
  ac_nf at a
  simp only [BitVec.reduceAdd] at a
  simp only [BitVec.add_zero] at a
  simp only [beq_self_eq_true] at a
  simp only [Bool.not_true] at a
  /-
  case h
  x y : BitVec 32
  a : false = true
  ⊢ False
  -/
  simp only [Bool.false_eq_true] at a -- here the proof hangs

/--
This one is fast.
-/
theorem test (x y : BitVec 32) (a : false = true ) :
    False := by
  simp only [Bool.false_eq_true] at a
