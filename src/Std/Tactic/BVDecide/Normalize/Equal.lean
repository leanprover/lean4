/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Init.Data.Bool
import Init.Data.BitVec

/-!
This module contains the equality simplifying part of the `bv_normalize` simp set.
-/

namespace Std.Tactic.BVDecide
namespace Frontend.Normalize

attribute [bv_normalize] eq_self
attribute [bv_normalize] beq_self_eq_true
attribute [bv_normalize] beq_self_eq_true'

@[bv_normalize]
theorem Bool.not_beq_not : ∀ (a b : Bool), ((!a) == (!b)) = (a == b) := by
  decide

@[bv_normalize]
theorem BitVec.not_beq_not (a b : BitVec w) : (~~~a == ~~~b) = (a == b) := by
  rw [Bool.eq_iff_iff]
  simp

@[bv_normalize]
theorem BitVec.or_beq_zero_iff (a b : BitVec w) : (a ||| b == 0#w) = (a == 0#w && b == 0#w) := by
  rw [Bool.eq_iff_iff]
  simp

@[bv_normalize]
theorem BitVec.zero_beq_or_iff (a b : BitVec w) : (0#w == a ||| b) = (a == 0#w && b == 0#w) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, Eq.comm]
  simp

@[bv_normalize]
theorem BitVec.xor_beq_zero_iff (a b : BitVec w) : (a ^^^ b == 0#w) = (a == b) := by
  rw [Bool.eq_iff_iff]
  simp

@[bv_normalize]
theorem BitVec.zero_beq_xor_iff (a b : BitVec w) : (0#w == a ^^^ b) = (a == b) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, Eq.comm]
  simp

@[bv_normalize]
theorem BitVec.xor_left_inj (a b c : BitVec w) : (a ^^^ c == b ^^^ c) = (a == b) := by
  rw [Bool.eq_iff_iff]
  simp

@[bv_normalize]
theorem BitVec.xor_left_inj' (a b c : BitVec w) : (a ^^^ c == c ^^^ b) = (a == b) := by
  rw [Bool.eq_iff_iff, BitVec.xor_comm c]
  simp

@[bv_normalize]
theorem BitVec.xor_right_inj (a b c : BitVec w) : (c ^^^ a == c ^^^ b) = (a == b) := by
  rw [Bool.eq_iff_iff]
  simp

@[bv_normalize]
theorem BitVec.xor_right_inj' (a b c : BitVec w) : (c ^^^ a == b ^^^ c) = (a == b) := by
  rw [Bool.eq_iff_iff, BitVec.xor_comm c]
  simp

@[bv_normalize]
theorem BitVec.add_left_inj (a b c : BitVec w) : (a + c == b + c) = (a == b) := by
  rw [Bool.eq_iff_iff]
  simp

@[bv_normalize]
theorem BitVec.add_left_inj' (a b c : BitVec w) : (a + c == c + b) = (a == b) := by
  rw [BitVec.add_comm c b, add_left_inj]

@[bv_normalize]
theorem BitVec.add_right_inj (a b c : BitVec w) : (c + a == c + b) = (a == b) := by
  rw [Bool.eq_iff_iff]
  simp

@[bv_normalize]
theorem BitVec.add_right_inj' (a b c : BitVec w) : (c + a == b + c) = (a == b) := by
  rw [BitVec.add_comm b c, add_right_inj]

@[bv_normalize]
theorem BitVec.add_left_eq_self (a b : BitVec w) : (a + b == b) = (a == 0#w) := by
  rw [Bool.eq_iff_iff]
  simp

@[bv_normalize]
theorem BitVec.add_right_eq_self (a b : BitVec w) : (a + b == a) = (b == 0#w) := by
  rw [Bool.eq_iff_iff]
  simp

@[bv_normalize]
theorem BitVec.self_eq_add_right (a b : BitVec w) : (a == a + b) = (b == 0#w) := by
  rw [Bool.eq_iff_iff]
  simp

@[bv_normalize]
theorem BitVec.self_eq_add_left (a b : BitVec w) : (a == b + a) = (b == 0#w) := by
  rw [Bool.eq_iff_iff]
  simp

@[bv_normalize]
theorem BitVec.eq_sub_iff_add_eq (a b c : BitVec w) : (a == c + (~~~b + 1#w)) = (a + b == c) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, ← BitVec.neg_eq_not_add, ← @BitVec.sub_toAdd]
  exact _root_.BitVec.eq_sub_iff_add_eq

@[bv_normalize]
theorem BitVec.eq_neg_add_iff_add_eq (a b c : BitVec w) : (a == (~~~b + 1#w) + c) = (a + b == c) := by
  rw [BitVec.add_comm]
  exact BitVec.eq_sub_iff_add_eq _ _ _

@[bv_normalize]
theorem BitVec.sub_eq_iff_eq_add (a b c : BitVec w) : (a + (~~~b + 1#w) == c) = (a == c + b) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, ← BitVec.neg_eq_not_add, ← @BitVec.sub_toAdd]
  exact _root_.BitVec.sub_eq_iff_eq_add

@[bv_normalize]
theorem BitVec.neg_add_eq_iff_eq_add (a b c : BitVec w) : ((~~~a + 1#w) + b == c) = (b == c + a) := by
  rw [BitVec.add_comm]
  exact BitVec.sub_eq_iff_eq_add _ _ _

end Frontend.Normalize
end Std.Tactic.BVDecide
