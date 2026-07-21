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
Homomorphism rules for `UInt16` used by the `grind` tactic.
The injection function is `UInt16.toBitVec`.
-/

attribute [grind hom]
  UInt16.toBitVec_add UInt16.toBitVec_sub UInt16.toBitVec_mul UInt16.toBitVec_div UInt16.toBitVec_mod
  UInt16.toBitVec_and UInt16.toBitVec_or UInt16.toBitVec_xor UInt16.toBitVec_shiftLeft UInt16.toBitVec_shiftRight
  UInt16.toBitVec_zero UInt16.toBitVec_one UInt16.toBitVec_not UInt16.toBitVec_neg
  UInt16.eq_iff_toBitVec_eq
  UInt16.toBitVec_ofNat UInt16.toBitVec_ofNat'
  UInt16.toBitVec_toUInt8 UInt16.toBitVec_toUInt32 UInt16.toBitVec_toUInt64 UInt16.toBitVec_toUSize UInt16.toBitVec_toInt16

@[grind hom] theorem Lean.Grind.UInt16.toNat_eq_toBitVec_toNat (x : UInt16) : x.toNat = x.toBitVec.toNat := rfl

/-! Translations of `≤` and `<` into the target domain. -/

attribute [grind hom] UInt16.le_iff_toBitVec_le UInt16.lt_iff_toBitVec_lt
