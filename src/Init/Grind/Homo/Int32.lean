/-
Copyright (c) 2026 Andres Erbsen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Erbsen, Leonardo de Moura
-/
module
prelude
import Init.Grind.Attr
public import Init.Data.UInt.Lemmas
public import Init.Data.UInt.Bitwise
public import Init.Data.SInt.Lemmas
public import Init.Data.SInt.Bitwise
public section

/-!
Homomorphism rules for `Int32` used by the `grind` tactic.
The injection function is `Int32.toBitVec`.
-/

attribute [grind hom]
  Int32.toBitVec_add Int32.toBitVec_sub Int32.toBitVec_mul Int32.toBitVec_div Int32.toBitVec_mod
  Int32.toBitVec_and Int32.toBitVec_or Int32.toBitVec_xor Int32.toBitVec_shiftLeft Int32.toBitVec_shiftRight
  Int32.toBitVec_zero Int32.toBitVec_one Int32.toBitVec_not Int32.toBitVec_neg
  Int32.eq_iff_toBitVec_eq
  Int32.toBitVec_ofNat
  Int32.toBitVec_toInt8 Int32.toBitVec_toInt16 Int32.toBitVec_toInt64 Int32.toBitVec_toISize Int32.toBitVec_toUInt32

@[grind hom] theorem Lean.Grind.Int32.toInt_eq_toBitVec_toInt (x : Int32) : x.toInt = x.toBitVec.toInt := rfl

/-! Translations of `≤` and `<` into the target domain. -/

attribute [grind hom] Int32.le_iff_toInt_le Int32.lt_iff_toInt_lt
