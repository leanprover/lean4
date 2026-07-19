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

/-!
Homomorphism rules for `BitVec` used by the `grind` tactic.
The unsigned fragment is injected into `Nat` via `BitVec.toNat`, and the signed
fragment into `Int` via `BitVec.toInt`.
-/

attribute [grind homo]
  BitVec.toNat_add BitVec.toNat_sub BitVec.toNat_mul BitVec.toNat_udiv BitVec.toNat_umod
  BitVec.toNat_neg BitVec.toNat_and BitVec.toNat_or BitVec.toNat_xor
  BitVec.toNat_shiftLeft BitVec.toNat_ushiftRight BitVec.toNat_append
  BitVec.toNat_ofNat BitVec.ofNat_toNat BitVec.toNat_setWidth
  BitVec.toNat_eq BitVec.le_def BitVec.lt_def
  BitVec.sle_iff_toInt_le BitVec.slt_iff_toInt_lt
  BitVec.toInt_add BitVec.toInt_sub BitVec.toInt_mul BitVec.toInt_neg
  BitVec.toInt_not BitVec.toInt_shiftLeft BitVec.toInt_sshiftRight
  BitVec.toInt_sdiv BitVec.toInt_srem BitVec.toInt_smod
  BitVec.setWidth_eq
  BitVec.xor_allOnes BitVec.allOnes_and BitVec.and_allOnes BitVec.not_zero
  BitVec.zero_and BitVec.and_zero BitVec.zero_or BitVec.or_zero
  BitVec.zero_xor BitVec.xor_zero BitVec.xor_self

/-! Homomorphism predicates: range facts for the injection functions, instantiated by
`grind` for the terms it internalizes. The `2 * toInt` bounds are restated with an
explicit parameter, as required by the `[grind homo_pred]` trigger inference. -/

attribute [grind homo_pred] BitVec.isLt

@[grind homo_pred] theorem Lean.Grind.BitVec.neg_two_pow_le_two_mul_toInt {w : Nat} (x : BitVec w) :
    -2^w ≤ 2 * x.toInt :=
  _root_.BitVec.le_two_mul_toInt

@[grind homo_pred] theorem Lean.Grind.BitVec.two_mul_toInt_lt_two_pow {w : Nat} (x : BitVec w) :
    2 * x.toInt < 2^w :=
  _root_.BitVec.two_mul_toInt_lt
