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
import Init.Data.SInt.Basic

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

attribute [bv_normalize] BitVec.zeroExtend_eq_setWidth
attribute [bv_normalize] BitVec.truncate_eq_setWidth

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
theorem BitVec.ofNatLT_reduce (n : Nat) (h) : BitVec.ofNatLT n h = BitVec.ofNat w n := by
  simp [BitVec.ofNatLT, BitVec.ofNat, Fin.ofNat', Nat.mod_eq_of_lt h]

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
attribute [bv_normalize] BitVec.getLsbD_eq_extractLsb'

end Reduce

section Constant

attribute [bv_normalize] BitVec.add_zero
attribute [bv_normalize] BitVec.zero_add
attribute [bv_normalize] BitVec.mul_one
attribute [bv_normalize] BitVec.one_mul
attribute [bv_normalize] BitVec.not_not

attribute [bv_normalize] decide_true
attribute [bv_normalize] decide_false
attribute [bv_normalize] decide_not
attribute [bv_normalize] BitVec.cast_eq

end Constant

attribute [bv_normalize] BitVec.zero_and
attribute [bv_normalize] BitVec.and_zero

attribute [bv_normalize] BitVec.intMax
attribute [bv_normalize] BitVec.intMin

-- Used in simproc because of - normalization
theorem BitVec.ones_and (a : BitVec w) : (-1#w) &&& a = a := by
  ext
  simp [BitVec.neg_one_eq_allOnes]

-- Used in simproc because of - normalization
theorem BitVec.and_ones (a : BitVec w) : a &&& (-1#w) = a := by
  ext
  simp [BitVec.neg_one_eq_allOnes]

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
  simp [BitVec.neg_one_eq_allOnes]

@[bv_normalize]
theorem BitVec.not_add (a : BitVec w) : ~~~a + a = (-1#w) := by
  rw [BitVec.add_comm]
  rw [BitVec.add_not]

@[bv_normalize]
theorem BitVec.add_neg (a : BitVec w) : a + (~~~a + 1#w) = 0#w := by
  rw [← BitVec.neg_eq_not_add]
  rw [← BitVec.sub_eq_add_neg]
  rw [BitVec.sub_self]

@[bv_normalize]
theorem BitVec.neg_add (a : BitVec w) : (~~~a + 1#w) + a = 0#w := by
  rw [← BitVec.neg_eq_not_add]
  rw [BitVec.add_comm]
  rw [← BitVec.sub_eq_add_neg]
  rw [BitVec.sub_self]

@[bv_normalize]
theorem BitVec.not_neg (x : BitVec w) : ~~~(~~~x + 1#w) = x + -1#w := by
  rw [← BitVec.neg_eq_not_add x]
  rw [_root_.BitVec.not_neg, BitVec.sub_eq_add_neg]

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

@[bv_normalize]
theorem BitVec.add_const_left :
    BitVec.ofNat w a + (BitVec.ofNat w b + c) = (BitVec.ofNat w a + BitVec.ofNat w b) + c := by
  ac_rfl

@[bv_normalize]
theorem BitVec.add_const_right :
    BitVec.ofNat w a + (b + BitVec.ofNat w c) = (BitVec.ofNat w a + BitVec.ofNat w c) + b := by
  ac_rfl

@[bv_normalize]
theorem BitVec.add_const_left' :
    (BitVec.ofNat w a + b) + BitVec.ofNat w c = (BitVec.ofNat w a + BitVec.ofNat w c) + b := by
  ac_rfl

@[bv_normalize]
theorem BitVec.add_const_right' {a : BitVec w} :
    (a + BitVec.ofNat w b) + BitVec.ofNat w c = (BitVec.ofNat w b + BitVec.ofNat w c) + a := by
  ac_rfl

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

@[bv_normalize]
theorem BitVec.shiftLeft_neg {x : BitVec w₁} {y : BitVec w₂} :
    (~~~x + 1#w₁) <<< y = ~~~(x <<< y) + 1 := by
  simp [← BitVec.neg_eq_not_add, _root_.BitVec.shiftLeft_neg]

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
  rw [BitVec.neg_one_eq_allOnes, ← Bool.not_eq_true, ← @lt_ult]
  exact BitVec.not_allOnes_lt

theorem BitVec.ult_max' (a : BitVec w) : (BitVec.ult a (-1#w)) = (!(a == -1#w)) := by
  have := BitVec.lt_allOnes_iff (x := a)
  rw [lt_ult, ← BitVec.neg_one_eq_allOnes] at this
  by_cases (a.ult (-1#w)) <;> simp_all

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

attribute [bv_normalize] BitVec.saddOverflow_eq
attribute [bv_normalize] BitVec.uaddOverflow_eq
attribute [bv_normalize] BitVec.negOverflow_eq
attribute [bv_normalize] BitVec.umulOverflow_eq
attribute [bv_normalize] BitVec.smulOverflow_eq
attribute [bv_normalize] BitVec.usubOverflow_eq
attribute [bv_normalize] BitVec.ssubOverflow_eq
attribute [bv_normalize] BitVec.sdivOverflow_eq

/-- `x / (BitVec.ofNat n)` where `n = 2^k` is the same as shifting `x` right by `k`. -/
theorem BitVec.udiv_ofNat_eq_of_lt (w : Nat) (x : BitVec w) (n : Nat) (k : Nat) (hk : 2 ^ k = n) (hlt : k < w) :
    x / (BitVec.ofNat w n) = x >>> k := by
  have : BitVec.ofNat w n = BitVec.twoPow w k := by simp [bitvec_to_nat, hk]
  rw [this, BitVec.udiv_twoPow_eq_of_lt (hk := by omega)]

attribute [bv_normalize] BitVec.extractLsb'_and
attribute [bv_normalize] BitVec.extractLsb'_xor

@[bv_normalize]
theorem BitVec.exctractLsb'_if {x y : BitVec w} (s l : Nat) :
    BitVec.extractLsb' s l (bif c then x else y) = bif c then (BitVec.extractLsb' s l x) else (BitVec.extractLsb' s l y) := by
  cases c <;> simp

attribute [bv_normalize] BitVec.extractLsb'_eq_self

-- Used in simproc because of - normalization
theorem BitVec.ones_mul (a : BitVec w) : -1#w * a = -a := by
  rw [_root_.BitVec.neg_mul]
  simp

-- Used in simproc because of - normalization
theorem BitVec.mul_ones (a : BitVec w) : a * -1#w = -a := by
  rw [_root_.BitVec.mul_neg]
  simp

-- All push a to the lhs as the rhs is guaranteed to be a constant so this form improves sharing.
@[bv_normalize]
theorem BitVec.add_const_beq_const {a : BitVec w} :
    ((a + BitVec.ofNat w b) == BitVec.ofNat w c) = (a == BitVec.ofNat w c - BitVec.ofNat w b) := by
  rw [Bool.eq_iff_iff]
  simp [BitVec.eq_sub_iff_add_eq]

@[bv_normalize]
theorem BitVec.const_add_beq_const :
    ((BitVec.ofNat w b + a) == BitVec.ofNat w c) = (a == BitVec.ofNat w c - BitVec.ofNat w b) := by
  rw [Bool.eq_iff_iff, BitVec.add_comm _ a]
  simp [BitVec.eq_sub_iff_add_eq]

@[bv_normalize]
theorem BitVec.const_beq_add_const_beq :
    (BitVec.ofNat w c == (a + BitVec.ofNat w b)) = (a == BitVec.ofNat w c - BitVec.ofNat w b) := by
  rw [Bool.eq_iff_iff, Bool.beq_comm]
  simp [BitVec.eq_sub_iff_add_eq]

@[bv_normalize]
theorem BitVec.const_beq_const_add_beq :
    (BitVec.ofNat w c == (BitVec.ofNat w b + a)) = (a == BitVec.ofNat w c - BitVec.ofNat w b) := by
  rw [Bool.eq_iff_iff, BitVec.add_comm _ a, Bool.beq_comm]
  simp [BitVec.eq_sub_iff_add_eq]

@[bv_normalize]
theorem BitVec.and_const_left :
    BitVec.ofNat w a &&& (BitVec.ofNat w b &&& c) = (BitVec.ofNat w a &&& BitVec.ofNat w b) &&& c := by
  ac_rfl

@[bv_normalize]
theorem BitVec.and_const_right :
    BitVec.ofNat w a &&& (b &&& BitVec.ofNat w c) = (BitVec.ofNat w a &&& BitVec.ofNat w c) &&& b := by
  ac_rfl

@[bv_normalize]
theorem BitVec.and_const_left' :
    (BitVec.ofNat w a &&& b) &&& BitVec.ofNat w c = (BitVec.ofNat w a &&& BitVec.ofNat w c) &&& b := by
  ac_rfl

@[bv_normalize]
theorem BitVec.and_const_right' {a : BitVec w} :
    (a &&& BitVec.ofNat w b) &&& BitVec.ofNat w c = (BitVec.ofNat w b &&& BitVec.ofNat w c) &&& a := by
  ac_rfl

-- Explicit no_index so this theorem works in the presence of constant folding if w1/w2/w3 are fixed
@[bv_normalize]
theorem BitVec.append_const_left {c : BitVec w3} :
    HAppend.hAppend (β := BitVec (no_index _)) (γ := BitVec (no_index _))
      (BitVec.ofNat w1 a)
      (HAppend.hAppend (γ := BitVec (no_index _)) (BitVec.ofNat w2 b) c)
    = ((BitVec.ofNat w1 a ++ BitVec.ofNat w2 b) ++ c).cast (Nat.add_assoc ..) := by
  rw [BitVec.append_assoc]
  simp

@[bv_normalize]
theorem BitVec.append_const_right {a : BitVec w1} :
    HAppend.hAppend (α := BitVec (no_index _)) (γ := BitVec (no_index _))
      (HAppend.hAppend (γ := BitVec (no_index _)) a (BitVec.ofNat w2 b))
      (BitVec.ofNat w3 c)
    = (a ++ (BitVec.ofNat w2 b ++ BitVec.ofNat w3 c)).cast (Eq.symm <| Nat.add_assoc ..) := by
  rw [BitVec.append_assoc]

theorem BitVec.signExtend_elim {v : Nat} {x : BitVec v} {w : Nat} (h : v ≤ w) :
    BitVec.signExtend w x = ((bif x.msb then -1#(w - v) else 0#(w - v)) ++ x).cast (by omega) := by
  rw [BitVec.signExtend_eq_append_of_le]
  simp [BitVec.neg_one_eq_allOnes, cond_eq_if]
  assumption

theorem BitVec.signExtend_elim' {v : Nat} {x : BitVec v} {w : Nat} (h : w ≤ v) :
    BitVec.signExtend w x = BitVec.extractLsb' 0 w x := by
  rw [BitVec.signExtend_eq_setWidth_of_le _ h, BitVec.setWidth_eq_extractLsb' h]

@[bv_normalize]
theorem BitVec.add_neg_mul {x y : BitVec w} : ~~~(x + x * y) + 1#w = x * ~~~y := by
  rw [← BitVec.neg_eq_not_add, BitVec.neg_add_mul_eq_mul_not]

@[bv_normalize]
theorem BitVec.add_neg_mul' {x y : BitVec w} : ~~~(x + y * x) + 1#w = ~~~y * x := by
  rw [BitVec.mul_comm y x, BitVec.mul_comm (~~~y) x, BitVec.add_neg_mul]

@[bv_normalize]
theorem BitVec.add_neg_mul'' {x y : BitVec w} : ~~~(x * y + x) + 1#w = x * ~~~y := by
  rw [BitVec.add_comm (x * y) x, BitVec.add_neg_mul]

@[bv_normalize]
theorem BitVec.add_neg_mul''' {x y : BitVec w} : ~~~(y * x + x) + 1#w = ~~~y * x := by
  rw [BitVec.mul_comm y x, BitVec.mul_comm (~~~y) x,BitVec.add_neg_mul'']

@[bv_normalize]
theorem BitVec.norm_bv_add_mul {x y : BitVec w} : ~~~(x * ~~~y) + 1#w = x + (x * y) := by
  rw [← BitVec.neg_eq_not_add, BitVec.neg_mul_not_eq_add_mul]

@[bv_normalize]
theorem BitVec.norm_bv_add_mul' {x y : BitVec w} : ~~~(~~~y * x) + 1#w = x + (y * x) := by
  rw [BitVec.mul_comm (~~~y) x, BitVec.mul_comm y x, BitVec.norm_bv_add_mul]

theorem BitVec.mul_beq_mul_short_circuit_left {x₁ x₂ y : BitVec w} :
    (x₁ * y == x₂ * y) = !(!x₁ == x₂ && !x₁ * y == x₂ * y) := by
  simp only [Bool.not_and, Bool.not_not, Bool.eq_or_self, beq_iff_eq]
  intros
  congr

theorem BitVec.mul_beq_mul_short_circuit_right {x y₁ y₂ : BitVec w} :
    (x * y₁ == x * y₂) = !(!y₁ == y₂ && !x * y₁ == x * y₂) := by
  simp only [Bool.not_and, Bool.not_not, Bool.eq_or_self, beq_iff_eq]
  intros
  congr

@[int_toBitVec]
theorem UInt8.toBitVec_cond :
    UInt8.toBitVec (bif c then t else e) = bif c then t.toBitVec else e.toBitVec := by
  rw [Bool.apply_cond UInt8.toBitVec]

@[int_toBitVec]
theorem UInt16.toBitVec_cond :
    UInt16.toBitVec (bif c then t else e) = bif c then t.toBitVec else e.toBitVec := by
  rw [Bool.apply_cond UInt16.toBitVec]

@[int_toBitVec]
theorem UInt32.toBitVec_cond :
    UInt32.toBitVec (bif c then t else e) = bif c then t.toBitVec else e.toBitVec := by
  rw [Bool.apply_cond UInt32.toBitVec]

@[int_toBitVec]
theorem UInt64.toBitVec_cond :
    UInt64.toBitVec (bif c then t else e) = bif c then t.toBitVec else e.toBitVec := by
  rw [Bool.apply_cond UInt64.toBitVec]

@[int_toBitVec]
theorem USize.toBitVec_cond :
    USize.toBitVec (bif c then t else e) = bif c then t.toBitVec else e.toBitVec := by
  rw [Bool.apply_cond USize.toBitVec]

@[int_toBitVec]
theorem Int8.toBitVec_cond :
    Int8.toBitVec (bif c then t else e) = bif c then t.toBitVec else e.toBitVec := by
  rw [Bool.apply_cond Int8.toBitVec]

@[int_toBitVec]
theorem Int16.toBitVec_cond :
    Int16.toBitVec (bif c then t else e) = bif c then t.toBitVec else e.toBitVec := by
  rw [Bool.apply_cond Int16.toBitVec]

@[int_toBitVec]
theorem Int32.toBitVec_cond :
    Int32.toBitVec (bif c then t else e) = bif c then t.toBitVec else e.toBitVec := by
  rw [Bool.apply_cond Int32.toBitVec]

@[int_toBitVec]
theorem Int64.toBitVec_cond :
    Int64.toBitVec (bif c then t else e) = bif c then t.toBitVec else e.toBitVec := by
  rw [Bool.apply_cond Int64.toBitVec]

@[int_toBitVec]
theorem ISize.toBitVec_cond :
    ISize.toBitVec (bif c then t else e) = bif c then t.toBitVec else e.toBitVec := by
  rw [Bool.apply_cond ISize.toBitVec]

@[int_toBitVec]
theorem UInt8.toBitVec_ite [Decidable c] :
    UInt8.toBitVec (if c then t else e) = if c then t.toBitVec else e.toBitVec := by
  rw [apply_ite UInt8.toBitVec]

@[int_toBitVec]
theorem UInt16.toBitVec_ite [Decidable c] :
    UInt16.toBitVec (if c then t else e) = if c then t.toBitVec else e.toBitVec := by
  rw [apply_ite UInt16.toBitVec]

@[int_toBitVec]
theorem UInt32.toBitVec_ite [Decidable c] :
    UInt32.toBitVec (if c then t else e) = if c then t.toBitVec else e.toBitVec := by
  rw [apply_ite UInt32.toBitVec]

@[int_toBitVec]
theorem UInt64.toBitVec_ite [Decidable c] :
    UInt64.toBitVec (if c then t else e) = if c then t.toBitVec else e.toBitVec := by
  rw [apply_ite UInt64.toBitVec]

@[int_toBitVec]
theorem USize.toBitVec_ite [Decidable c] :
    USize.toBitVec (if c then t else e) = if c then t.toBitVec else e.toBitVec := by
  rw [apply_ite USize.toBitVec]

@[int_toBitVec]
theorem Int8.toBitVec_ite [Decidable c] :
    Int8.toBitVec (if c then t else e) = if c then t.toBitVec else e.toBitVec := by
  rw [apply_ite Int8.toBitVec]

@[int_toBitVec]
theorem Int16.toBitVec_ite [Decidable c] :
    Int16.toBitVec (if c then t else e) = if c then t.toBitVec else e.toBitVec := by
  rw [apply_ite Int16.toBitVec]

@[int_toBitVec]
theorem Int32.toBitVec_ite [Decidable c] :
    Int32.toBitVec (if c then t else e) = if c then t.toBitVec else e.toBitVec := by
  rw [apply_ite Int32.toBitVec]

@[int_toBitVec]
theorem Int64.toBitVec_ite [Decidable c] :
    Int64.toBitVec (if c then t else e) = if c then t.toBitVec else e.toBitVec := by
  rw [apply_ite Int64.toBitVec]

@[int_toBitVec]
theorem ISize.toBitVec_ite [Decidable c] :
    ISize.toBitVec (if c then t else e) = if c then t.toBitVec else e.toBitVec := by
  rw [apply_ite ISize.toBitVec]

end Normalize
end Std.Tactic.BVDecide
