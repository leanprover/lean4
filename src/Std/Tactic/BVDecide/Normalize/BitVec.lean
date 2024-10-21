/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Init.Data.BitVec.Bitblast
import Init.Data.AC
import Std.Tactic.BVDecide.Normalize.Bool
import Std.Tactic.BVDecide.Normalize.Canonicalize

/-!
This module contains the `BitVec` simplifying part of the `bv_normalize` simp set.
-/

namespace Std.Tactic.BVDecide
namespace Normalize


section Reduce

attribute [bv_normalize] BitVec.sub_toAdd

@[bv_normalize]
theorem BitVec.le_ult (x y : BitVec w) : (x ≤ y) = ¬(y < x) := by
  simp only [(· ≤ ·), (· < ·)]
  simp
attribute [bv_normalize] BitVec.ule_eq_not_ult

attribute [bv_normalize] gt_iff_lt
attribute [bv_normalize] ge_iff_le

@[bv_normalize]
theorem BitVec.truncate_eq_zeroExtend (x : BitVec w) : x.truncate n = x.zeroExtend n := by
  rfl

attribute [bv_normalize] BitVec.extractLsb
attribute [bv_normalize] BitVec.msb_eq_getLsbD_last
attribute [bv_normalize] BitVec.slt_eq_ult
attribute [bv_normalize] BitVec.sle_eq_not_slt

attribute [bv_normalize] BitVec.ofNat_eq_ofNat

@[bv_normalize]
theorem BitVec.ofNatLt_reduce (n : Nat) (h) : BitVec.ofNatLt n h = BitVec.ofNat w n := by
  simp [BitVec.ofNatLt, BitVec.ofNat, Fin.ofNat', Nat.mod_eq_of_lt h]

end Reduce

section Constant

attribute [bv_normalize] BitVec.add_zero
attribute [bv_normalize] BitVec.zero_add
attribute [bv_normalize] BitVec.setWidth_eq
attribute [bv_normalize] BitVec.setWidth_zero
attribute [bv_normalize] BitVec.getLsbD_zero
attribute [bv_normalize] BitVec.getLsbD_zero_length
attribute [bv_normalize] BitVec.getLsbD_concat_zero
attribute [bv_normalize] BitVec.mul_one
attribute [bv_normalize] BitVec.one_mul
attribute [bv_normalize] BitVec.not_not

end Constant

@[bv_normalize]
theorem BitVec.zero_and (a : BitVec w) : 0#w &&& a = 0#w := by
  ext
  simp

@[bv_normalize]
theorem BitVec.and_zero (a : BitVec w) : a &&& 0#w = 0#w := by
  ext
  simp

-- Used in simproc because of - normalization
theorem BitVec.ones_and (a : BitVec w) : (-1#w) &&& a = a := by
  ext
  simp [BitVec.negOne_eq_allOnes]

-- Used in simproc because of - normalization
theorem BitVec.and_ones (a : BitVec w) : a &&& (-1#w) = a := by
  ext
  simp [BitVec.negOne_eq_allOnes]

@[bv_normalize]
theorem BitVec.and_self (a : BitVec w) : a &&& a = a := by
  ext
  simp

@[bv_normalize]
theorem BitVec.and_contra (a : BitVec w) : a &&& ~~~a = 0#w := by
  ext
  simp

@[bv_normalize]
theorem BitVec.and_contra' (a : BitVec w) : ~~~a &&& a = 0#w := by
  ext
  simp

@[bv_normalize]
theorem BitVec.add_not (a : BitVec w) : a + ~~~a = (-1#w) := by
  ext
  simp [BitVec.negOne_eq_allOnes]

@[bv_normalize]
theorem BitVec.not_add (a : BitVec w) : ~~~a + a = (-1#w) := by
  rw [BitVec.add_comm]
  rw [BitVec.add_not]

@[bv_normalize]
theorem BitVec.add_neg (a : BitVec w) : a + (~~~a + 1#w) = 0#w := by
  rw [← BitVec.neg_eq_not_add]
  rw [← BitVec.sub_toAdd]
  rw [BitVec.sub_self]

@[bv_normalize]
theorem BitVec.add_neg' (a : BitVec w) : a + (1#w + ~~~a) = 0#w := by
  rw [BitVec.add_comm 1#w (~~~a)]
  rw [BitVec.add_neg]

@[bv_normalize]
theorem BitVec.neg_add (a : BitVec w) : (~~~a + 1#w) + a = 0#w := by
  rw [← BitVec.neg_eq_not_add]
  rw [BitVec.add_comm]
  rw [← BitVec.sub_toAdd]
  rw [BitVec.sub_self]

@[bv_normalize]
theorem BitVec.neg_add' (a : BitVec w) : (1#w + ~~~a) + a = 0#w := by
  rw [BitVec.add_comm 1#w (~~~a)]
  rw [BitVec.neg_add]

@[bv_normalize]
theorem BitVec.not_neg (x : BitVec w) : ~~~(~~~x + 1#w) = x + -1#w := by
  rw [← BitVec.neg_eq_not_add x]
  rw [_root_.BitVec.not_neg]

@[bv_normalize]
theorem BitVec.not_neg' (x : BitVec w) : ~~~(1#w + ~~~x) = x + -1#w := by
  rw [BitVec.add_comm 1#w (~~~x)]
  rw [BitVec.not_neg]

@[bv_normalize]
theorem BitVec.not_neg'' (x : BitVec w) : ~~~(x + 1#w) = ~~~x + -1#w := by
  rw [← BitVec.not_not (b := x)]
  rw [BitVec.not_neg]
  simp

@[bv_normalize]
theorem BitVec.not_neg''' (x : BitVec w) : ~~~(1#w + x) = ~~~x + -1#w := by
  rw [BitVec.add_comm 1#w x]
  rw [BitVec.not_neg'']

@[bv_normalize]
theorem BitVec.add_same (a : BitVec w) : a + a = a * 2#w := by
  rw [BitVec.mul_two]

theorem BitVec.add_const_left (a b c : BitVec w) : a + (b + c) = (a + b) + c := by ac_rfl
theorem BitVec.add_const_right (a b c : BitVec w) : a + (b + c) = (a + c) + b := by ac_rfl
theorem BitVec.add_const_left' (a b c : BitVec w) : (a + b) + c = (a + c) + b := by ac_rfl
theorem BitVec.add_const_right' (a b c : BitVec w) : (a + b) + c = (b + c) + a := by ac_rfl

@[bv_normalize]
theorem BitVec.zero_sshiftRight : BitVec.sshiftRight 0#w a = 0#w := by
  ext
  simp [BitVec.getLsbD_sshiftRight]

@[bv_normalize]
theorem BitVec.sshiftRight_zero : BitVec.sshiftRight a 0 = a := by
  ext
  simp [BitVec.getLsbD_sshiftRight]

@[bv_normalize]
theorem BitVec.mul_zero (a : BitVec w) : a * 0#w = 0#w := by
  simp [bv_toNat]

@[bv_normalize]
theorem BitVec.zero_mul (a : BitVec w) : 0#w * a = 0#w := by
  simp [bv_toNat]

@[bv_normalize]
theorem BitVec.shiftLeft_zero (n : BitVec w) : n <<< 0#w' = n := by
  ext i
  simp only [(· <<< ·)]
  simp

@[bv_normalize]
theorem BitVec.shiftLeft_zero' (n : BitVec w) : n <<< 0 = n := by
  ext i
  simp

@[bv_normalize]
theorem BitVec.zero_shiftLeft (n : Nat) : 0#w <<< n = 0#w := by
  ext
  simp

@[bv_normalize]
theorem BitVec.zero_shiftRight (n : Nat) : 0#w >>> n = 0#w := by
  ext
  simp

@[bv_normalize]
theorem BitVec.shiftRight_zero (n : BitVec w) : n >>> 0#w' = n := by
  ext i
  simp only [(· >>> ·)]
  simp

@[bv_normalize]
theorem BitVec.shiftRight_zero' (n : BitVec w) : n >>> 0 = n := by
  ext i
  simp

theorem BitVec.zero_lt_iff_zero_neq (a : BitVec w) : (0#w < a) ↔ (a ≠ 0#w) := by
  constructor <;>
    simp_all only [BitVec.lt_def, BitVec.toNat_ofNat, Nat.zero_mod, ne_eq, BitVec.toNat_eq] <;>
    omega

@[bv_normalize]
theorem BitVec.zero_ult' (a : BitVec w) : (BitVec.ult 0#w a) = (a != 0#w) := by
  have := BitVec.zero_lt_iff_zero_neq a
  rw [BitVec.lt_ult] at this
  match h:BitVec.ult 0#w a with
  | true => simp_all
  | false => simp_all

theorem BitVec.max_ult (a : BitVec w) : ¬ ((-1#w) < a) := by
  rcases w with rfl | w
  · simp [bv_toNat, BitVec.toNat_of_zero_length]
  · simp only [BitVec.lt_def, BitVec.toNat_neg, BitVec.toNat_ofNat, Nat.not_lt]
    rw [Nat.mod_eq_of_lt (a := 1) (by simp)];
    rw [Nat.mod_eq_of_lt]
    · omega
    · apply Nat.sub_one_lt_of_le (Nat.pow_pos (by omega)) (Nat.le_refl ..)

@[bv_normalize]
theorem BitVec.max_ult' (a : BitVec w) : (BitVec.ult (-1#w) a) = false := by
  have := BitVec.max_ult a
  rw [BitVec.lt_ult] at this
  simp [this]

attribute [bv_normalize] BitVec.replicate_zero_eq

@[bv_normalize]
theorem BitVec.ofBool_getLsbD (a : BitVec w) (i : Nat) :
    BitVec.ofBool (a.getLsbD i) = a.extractLsb' i 1 := by
  ext j
  simp

@[bv_normalize]
theorem BitVec.getElem_eq_getLsbD (a : BitVec w) (i : Nat) (h : i < w) :
    a[i] = a.getLsbD i := by
  simp [BitVec.getLsbD_eq_getElem?_getD, BitVec.getElem?_eq, h]

attribute [bv_normalize] BitVec.add_eq_xor
attribute [bv_normalize] BitVec.mul_eq_and

attribute [bv_normalize] BitVec.zero_udiv
attribute [bv_normalize] BitVec.udiv_zero
attribute [bv_normalize] BitVec.udiv_one
attribute [bv_normalize] BitVec.udiv_eq_and
attribute [bv_normalize] BitVec.zero_umod
attribute [bv_normalize] BitVec.umod_zero
attribute [bv_normalize] BitVec.umod_one
attribute [bv_normalize] BitVec.umod_eq_and

end Normalize
end Std.Tactic.BVDecide
