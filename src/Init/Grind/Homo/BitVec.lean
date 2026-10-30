/-
Copyright (c) 2026 Andres Erbsen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Erbsen, Leonardo de Moura
-/
module
prelude
import Init.Grind.Attr
public import Init.Data.BitVec.Bootstrap
public import Init.Data.BitVec.Lemmas
public import Init.Data.BitVec.Bitblast
public section

/-!
Homomorphism rules for `BitVec` used by the `grind` tactic.
The unsigned fragment is injected into `Nat` via `BitVec.toNat`, and the signed
fragment into `Int` via `BitVec.toInt`.
-/

attribute [grind hom]
  BitVec.toNat_add BitVec.toNat_mul BitVec.toNat_udiv BitVec.toNat_umod
  BitVec.toNat_neg BitVec.toNat_and BitVec.toNat_or BitVec.toNat_xor
  BitVec.toNat_shiftLeft BitVec.toNat_ushiftRight BitVec.toNat_append_eq_mul_add
  BitVec.ofNat_toNat BitVec.toNat_setWidth BitVec.toNat_ofInt
  BitVec.toNat_eq BitVec.le_def BitVec.lt_def
  BitVec.sle_eq_decide BitVec.slt_eq_decide
  BitVec.toInt_add BitVec.toInt_sub BitVec.toInt_mul BitVec.toInt_neg
  BitVec.toInt_not BitVec.toInt_shiftLeft_eq_toInt_shiftLeft_bmod BitVec.toInt_sshiftRight
  BitVec.toInt_sdiv BitVec.toInt_srem BitVec.toInt_smod
  BitVec.setWidth_eq
  BitVec.xor_allOnes BitVec.allOnes_and BitVec.and_allOnes BitVec.not_zero
  BitVec.zero_and BitVec.and_zero BitVec.zero_or BitVec.or_zero
  BitVec.zero_xor BitVec.xor_zero BitVec.xor_self
  BitVec.toInt_signExtend BitVec.toInt_setWidth
  BitVec.toNat_pow BitVec.toInt_pow
  BitVec.toNat_rotateLeft_eq_add BitVec.toNat_rotateRight_eq_add
  BitVec.toNat_sshiftRight_eq_toNat_emod

/- `grind` keeps `BitVec` literals in `OfNat.ofNat` form, so the rule must be stated in
this form for the structural `Sym.simp` retrieval to find it. -/
@[grind hom] theorem Lean.Grind.BitVec.toNat_OfNat_ofNat (n a : Nat) :
    (OfNat.ofNat a : BitVec n).toNat = a % 2 ^ n := by
  dsimp [OfNat.ofNat]
  exact BitVec.toNat_ofNat ..

/-! `lia` treats `(x - y).toNat` as an atom. The following two rules relate it linearly to `x.toNat`
and `y.toNat`, one rule for each case of the wraparound. -/

theorem Lean.Grind.BitVec.toNat_sub_add_toNat_of_le {w : Nat} {x y : BitVec w}
    (h : y.toNat ≤ x.toNat) : (x - y).toNat + y.toNat = x.toNat := by
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr h), Nat.sub_add_cancel h]

theorem Lean.Grind.BitVec.toNat_sub_add_toNat_of_lt {w : Nat} {x y : BitVec w}
    (h : x.toNat < y.toNat) : (x - y).toNat + y.toNat = x.toNat + 2 ^ w := by
  have hdy : y.toNat - x.toNat ≤ y.toNat := Nat.sub_le _ _
  have hd : y.toNat - x.toNat ≤ 2 ^ w := Nat.le_trans hdy (Nat.le_of_lt y.isLt)
  rw [BitVec.toNat_sub_of_lt (BitVec.lt_def.mpr h), ← Nat.sub_add_comm hd,
    Nat.add_sub_assoc hdy, Nat.sub_sub_self (Nat.le_of_lt h), Nat.add_comm]

grind_pattern Lean.Grind.BitVec.toNat_sub_add_toNat_of_le => (x - y).toNat
grind_pattern Lean.Grind.BitVec.toNat_sub_add_toNat_of_lt => (x - y).toNat

/-! Homomorphism predicates: range facts for the injection functions, instantiated by
`grind` for the terms it internalizes. The `2 * toInt` bounds are restated with an
explicit parameter, as required by the `[grind hom_pred]` trigger inference. -/

attribute [grind hom_pred] BitVec.isLt

@[grind hom_pred] theorem Lean.Grind.BitVec.neg_two_pow_le_two_mul_toInt {w : Nat} (x : BitVec w) :
    -2^w ≤ 2 * x.toInt :=
  _root_.BitVec.le_two_mul_toInt

@[grind hom_pred] theorem Lean.Grind.BitVec.two_mul_toInt_lt_two_pow {w : Nat} (x : BitVec w) :
    2 * x.toInt < 2^w :=
  _root_.BitVec.two_mul_toInt_lt
