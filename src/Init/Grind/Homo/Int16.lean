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
Homomorphism rules for `Int16` used by the `grind` tactic.
The injection function is `Int16.toBitVec`.
-/

attribute [grind homo]
  Int16.toBitVec_add Int16.toBitVec_sub Int16.toBitVec_mul Int16.toBitVec_div Int16.toBitVec_mod
  Int16.toBitVec_and Int16.toBitVec_or Int16.toBitVec_xor Int16.toBitVec_shiftLeft Int16.toBitVec_shiftRight
  Int16.toBitVec_zero Int16.toBitVec_one Int16.toBitVec_not Int16.toBitVec_neg
  Int16.eq_iff_toBitVec_eq
  Int16.toBitVec_ofNat
  Int16.toBitVec_toInt8 Int16.toBitVec_toInt32 Int16.toBitVec_toInt64 Int16.toBitVec_toISize Int16.toBitVec_toUInt16

@[grind homo] theorem Lean.Grind.Int16.toInt_eq_toBitVec_toInt (x : Int16) : x.toInt = x.toBitVec.toInt := rfl

/-! Translations of `≤` and `<` into the target domain. -/

attribute [grind homo] Int16.le_iff_toInt_le Int16.lt_iff_toInt_lt
