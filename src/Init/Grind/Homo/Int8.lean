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
Homomorphism rules for `Int8` used by the `grind` tactic.
The injection function is `Int8.toBitVec`.
-/

attribute [grind homo]
  Int8.toBitVec_add Int8.toBitVec_sub Int8.toBitVec_mul Int8.toBitVec_div Int8.toBitVec_mod
  Int8.toBitVec_and Int8.toBitVec_or Int8.toBitVec_xor Int8.toBitVec_shiftLeft Int8.toBitVec_shiftRight
  Int8.toBitVec_zero Int8.toBitVec_one Int8.toBitVec_not Int8.toBitVec_neg
  Int8.eq_iff_toBitVec_eq
  Int8.toBitVec_ofNat
  Int8.toBitVec_toInt16 Int8.toBitVec_toInt32 Int8.toBitVec_toInt64 Int8.toBitVec_toISize Int8.toBitVec_toUInt8

@[grind homo] theorem Lean.Grind.Int8.toInt_eq_toBitVec_toInt (x : Int8) : x.toInt = x.toBitVec.toInt := rfl

/-! Translations of `≤` and `<` into the target domain. -/

attribute [grind homo] Int8.le_iff_toInt_le Int8.lt_iff_toInt_lt
