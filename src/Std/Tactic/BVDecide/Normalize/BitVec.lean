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
theorem BitVec.le_ult (x y : BitVec w) : (x ≤ y) ↔ ((!y.ult x) = true) := by
  have : x ≤ y ↔ (x.ule y = true) := by
    simp [BitVec.le_def, BitVec.ule]
  rw [this, BitVec.ule_eq_not_ult]

attribute [bv_normalize] BitVec.ule_eq_not_ult

@[bv_normalize]
theorem BitVec.gt_ult (x y : BitVec w) : x > y ↔ (y.ult x = true) := by
  simp [BitVec.lt_ult]

@[bv_normalize]
theorem BitVec.ge_ule (x y : BitVec w) : x ≥ y ↔ ((!x.ult y) = true) := by
  simp [BitVec.le_ult]

@[bv_normalize]
theorem BitVec.truncate_eq_zeroExtend (x : BitVec w) : x.truncate n = x.zeroExtend n := by
  rfl

attribute [bv_normalize] BitVec.extractLsb
attribute [bv_normalize] BitVec.msb_eq_getLsbD_last

@[bv_normalize]
theorem BitVec.slt_eq_ult (x y : BitVec w) :
    x.slt y = ((!x.getLsbD (w - 1) == y.getLsbD (w - 1)) ^^ x.ult y) := by
  simp [_root_.BitVec.slt_eq_ult, BitVec.msb_eq_getLsbD_last, Bool.bne_to_beq]

@[bv_normalize]
theorem BitVec.sle_eq_ult (x y : BitVec w) :
    x.sle y = !((!x.getLsbD (w - 1) == y.getLsbD (w - 1)) ^^ y.ult x) := by
  rw [BitVec.sle_eq_not_slt, BitVec.slt_eq_ult, Bool.beq_comm]

attribute [bv_normalize] BitVec.ofNat_eq_ofNat

@[bv_normalize]
theorem BitVec.ofNatLt_reduce (n : Nat) (h) : BitVec.ofNatLt n h = BitVec.ofNat w n := by
  simp [BitVec.ofNatLt, BitVec.ofNat, Fin.ofNat', Nat.mod_eq_of_lt h]

@[bv_normalize]
theorem BitVec.ofBool_eq_if (b : Bool) : BitVec.ofBool b = bif b then 1#1 else 0#1 := by
  revert b
  decide

@[bv_normalize]
theorem BitVec.sdiv_udiv (x y : BitVec w) :
    x.sdiv y =
      bif x.getLsbD (w - 1) then
        bif y.getLsbD (w - 1) then
          (-x) / (-y)
        else
          -((-x) / y)
      else
        bif y.getLsbD (w - 1) then
          -(x / (-y))
        else
          x / y := by
  rw [BitVec.sdiv_eq, ← BitVec.msb_eq_getLsbD_last, ← BitVec.msb_eq_getLsbD_last]
  cases x.msb <;> cases y.msb <;> simp

@[bv_normalize]
theorem BitVec.smod_umod (x y : BitVec w) :
    x.smod y =
      bif x.getLsbD (w - 1) then
        bif y.getLsbD (w - 1) then
          - ((- x) % (- y))
        else
          (bif (- x) % y == 0#w then (- x) % y else y - (- x) % y)
      else
        bif y.getLsbD (w - 1) then
          (bif x % (- y) == 0#w then x % (- y) else x % (- y) + y)
        else
          x.umod y := by
  rw [BitVec.smod_eq, ← BitVec.msb_eq_getLsbD_last, ← BitVec.msb_eq_getLsbD_last]
  cases x.msb <;> cases y.msb <;> simp

attribute [bv_normalize] BitVec.smtUDiv_eq

@[bv_normalize]
theorem BitVec.smtSDiv_smtUDiv (x y : BitVec w) :
    x.smtSDiv y =
      bif x.getLsbD (w - 1) then
        bif y.getLsbD (w - 1) then
          (-x).smtUDiv (-y)
        else
          -((-x).smtUDiv y)
      else
        bif y.getLsbD (w - 1) then
          -(x.smtUDiv (-y))
        else
          x.smtUDiv y := by
  rw [BitVec.smtSDiv_eq, ← BitVec.msb_eq_getLsbD_last, ← BitVec.msb_eq_getLsbD_last]
  cases x.msb <;> cases y.msb <;> simp

@[bv_normalize]
theorem BitVec.srem_umod (x y : BitVec w) :
    x.srem y =
      bif x.getLsbD (w - 1) then
        bif y.getLsbD (w - 1) then
          -((-x) % (-y))
        else
          -((-x) % y)
      else
        bif y.getLsbD (w - 1) then
          x % (-y)
        else
          x % y := by
  rw [BitVec.srem_eq, ← BitVec.msb_eq_getLsbD_last, ← BitVec.msb_eq_getLsbD_last]
  cases x.msb <;> cases y.msb <;> simp

@[bv_normalize]
theorem BitVec.abs_eq (x : BitVec w) : x.abs = bif x.getLsbD (w - 1) then -x else x := by
  simp [_root_.BitVec.abs_eq, BitVec.msb_eq_getLsbD_last]

attribute [bv_normalize] BitVec.twoPow_eq

@[bv_normalize]
theorem BitVec.getElem_eq_getLsbD (a : BitVec w) (i : Nat) (h : i < w) :
    a[i]'h = a.getLsbD i := by
  simp [BitVec.getLsbD_eq_getElem?_getD, BitVec.getElem?_eq, h]

-- The side condition about being in bounds gets resolved if i and w are constant.
attribute [bv_normalize] BitVec.getMsbD_eq_getLsbD

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

attribute [bv_normalize] decide_true
attribute [bv_normalize] decide_false
attribute [bv_normalize] decide_not

end Constant

attribute [bv_normalize] BitVec.zero_and
attribute [bv_normalize] BitVec.and_zero

-- Used in simproc because of - normalization
theorem BitVec.ones_and (a : BitVec w) : (-1#w) &&& a = a := by
  ext
  simp [BitVec.negOne_eq_allOnes]

-- Used in simproc because of - normalization
theorem BitVec.and_ones (a : BitVec w) : a &&& (-1#w) = a := by
  ext
  simp [BitVec.negOne_eq_allOnes]

-- Normalize (1#w + ~~~x) to (~~~x + 1#w) to limit the number of symmetries we need for theorems
-- related to negative BitVecs.
@[bv_normalize]
theorem BitVec.one_plus_not_eq_not_plus_one (x : BitVec w) : (1#w + ~~~x) = (~~~x + 1#w) := by
  rw [BitVec.add_comm]

attribute [bv_normalize] BitVec.and_self

@[bv_normalize]
theorem BitVec.and_contra (a : BitVec w) : a &&& ~~~a = 0#w := by
  ext i h
  simp [h]

@[bv_normalize]
theorem BitVec.and_contra' (a : BitVec w) : ~~~a &&& a = 0#w := by
  ext i h
  simp [h]

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
theorem BitVec.neg_add (a : BitVec w) : (~~~a + 1#w) + a = 0#w := by
  rw [← BitVec.neg_eq_not_add]
  rw [BitVec.add_comm]
  rw [← BitVec.sub_toAdd]
  rw [BitVec.sub_self]

@[bv_normalize]
theorem BitVec.not_neg (x : BitVec w) : ~~~(~~~x + 1#w) = x + -1#w := by
  rw [← BitVec.neg_eq_not_add x]
  rw [_root_.BitVec.not_neg]

@[bv_normalize]
theorem BitVec.not_neg' (x : BitVec w) : ~~~(x + 1#w) = ~~~x + -1#w := by
  rw [← BitVec.not_not (b := x)]
  rw [BitVec.not_neg]
  simp

@[bv_normalize]
theorem BitVec.not_neg'' (x : BitVec w) : ~~~(1#w + x) = ~~~x + -1#w := by
  rw [BitVec.add_comm 1#w x]
  rw [BitVec.not_neg']

@[bv_normalize]
theorem BitVec.add_same (a : BitVec w) : a + a = a * 2#w := by
  rw [BitVec.mul_two]

theorem BitVec.add_const_left (a b c : BitVec w) : a + (b + c) = (a + b) + c := by ac_rfl
theorem BitVec.add_const_right (a b c : BitVec w) : a + (b + c) = (a + c) + b := by ac_rfl
theorem BitVec.add_const_left' (a b c : BitVec w) : (a + b) + c = (a + c) + b := by ac_rfl
theorem BitVec.add_const_right' (a b c : BitVec w) : (a + b) + c = (b + c) + a := by ac_rfl

attribute [bv_normalize] BitVec.mul_zero
attribute [bv_normalize] BitVec.zero_mul


attribute [bv_normalize] BitVec.shiftLeft_ofNat_eq
attribute [bv_normalize] BitVec.ushiftRight_ofNat_eq
attribute [bv_normalize] BitVec.sshiftRight'_ofNat_eq_sshiftRight

@[bv_normalize]
theorem BitVec.neg_mul (x y : BitVec w) : (~~~x + 1#w) * y = ~~~(x * y) + 1#w := by
  rw [← BitVec.neg_eq_not_add, ← BitVec.neg_eq_not_add, _root_.BitVec.neg_mul]

@[bv_normalize]
theorem BitVec.mul_neg (x y : BitVec w) : x * (~~~y + 1#w) = ~~~(x * y) + 1#w := by
  rw [← BitVec.neg_eq_not_add, ← BitVec.neg_eq_not_add, _root_.BitVec.mul_neg]

attribute [bv_normalize] BitVec.shiftLeft_zero
attribute [bv_normalize] BitVec.zero_shiftLeft

@[bv_normalize]
theorem BitVec.shiftLeft_zero' (n : BitVec w) : n <<< 0#w' = n := by
  ext i
  simp only [(· <<< ·)]
  simp

attribute [bv_normalize] BitVec.zero_sshiftRight
attribute [bv_normalize] BitVec.sshiftRight_zero

attribute [bv_normalize] BitVec.zero_ushiftRight
attribute [bv_normalize] BitVec.ushiftRight_zero

@[bv_normalize]
theorem BitVec.ushiftRight_zero' (n : BitVec w) : n >>> 0#w' = n := by
  ext i
  simp only [(· >>> ·)]
  simp

@[bv_normalize]
theorem BitVec.ushiftRight_self (n : BitVec w) : n >>> n = 0#w := by
  simp

theorem BitVec.zero_lt_iff_zero_neq (a : BitVec w) : (0#w < a) ↔ (a ≠ 0#w) := by
  constructor <;>
    simp_all only [BitVec.lt_def, BitVec.toNat_ofNat, Nat.zero_mod, ne_eq, BitVec.toNat_eq] <;>
    omega

@[bv_normalize]
theorem BitVec.zero_ult' (a : BitVec w) : (BitVec.ult 0#w a) = (!a == 0#w) := by
  have := BitVec.zero_lt_iff_zero_neq a
  rw [BitVec.lt_ult] at this
  match h:BitVec.ult 0#w a with
  | true => simp_all
  | false => simp_all

@[bv_normalize]
theorem BitVec.lt_irrefl (a : BitVec n) : (BitVec.ult a a) = false := by
  rw [← Bool.not_eq_true, ← BitVec.lt_ult]
  exact _root_.BitVec.lt_irrefl _

@[bv_normalize]
theorem BitVec.not_lt_zero (a : BitVec n) : (BitVec.ult a 0#n) = false := by rfl

@[bv_normalize]
theorem BitVec.lt_one_iff (a : BitVec n) (h : 0 < n) : (BitVec.ult a 1#n) = (a == 0#n) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, ← BitVec.lt_ult]
  exact _root_.BitVec.lt_one_iff h

-- used in simproc because of -1#w normalisation
theorem BitVec.max_ult' (a : BitVec w) : (BitVec.ult (-1#w) a) = false := by
  rw [BitVec.negOne_eq_allOnes, ← Bool.not_eq_true, ← @lt_ult]
  exact BitVec.not_allOnes_lt

attribute [bv_normalize] BitVec.replicate_zero_eq
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

/-- `x / (BitVec.ofNat n)` where `n = 2^k` is the same as shifting `x` right by `k`. -/
theorem BitVec.udiv_ofNat_eq_of_lt (w : Nat) (x : BitVec w) (n : Nat) (k : Nat) (hk : 2 ^ k = n) (hlt : k < w) :
    x / (BitVec.ofNat w n) = x >>> k := by
  have : BitVec.ofNat w n = BitVec.twoPow w k := by simp [bv_toNat, hk]
  rw [this, BitVec.udiv_twoPow_eq_of_lt (hk := by omega)]

end Normalize
end Std.Tactic.BVDecide
