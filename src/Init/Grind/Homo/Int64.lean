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
Homomorphism rules for `Int64` used by the `grind` tactic.
The injection function is `Int64.toBitVec`.
-/

attribute [grind hom]
  Int64.toBitVec_add Int64.toBitVec_sub Int64.toBitVec_mul Int64.toBitVec_div Int64.toBitVec_mod
  Int64.toBitVec_and Int64.toBitVec_or Int64.toBitVec_xor Int64.toBitVec_shiftLeft Int64.toBitVec_shiftRight
  Int64.toBitVec_zero Int64.toBitVec_one Int64.toBitVec_not Int64.toBitVec_neg
  Int64.eq_iff_toBitVec_eq
  Int64.toBitVec_ofNat
  Int64.toBitVec_toInt8 Int64.toBitVec_toInt16 Int64.toBitVec_toInt32 Int64.toBitVec_toISize Int64.toBitVec_toUInt64

@[grind hom] theorem Lean.Grind.Int64.toInt_eq_toBitVec_toInt (x : Int64) : x.toInt = x.toBitVec.toInt := rfl

/-! Translations of `≤` and `<` into the target domain. -/

attribute [grind hom] Int64.le_iff_toInt_le Int64.lt_iff_toInt_lt
