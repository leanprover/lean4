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
Homomorphism rules for `UInt64` used by the `grind` tactic.
The injection function is `UInt64.toBitVec`.
-/

attribute [grind hom]
  UInt64.toBitVec_add UInt64.toBitVec_sub UInt64.toBitVec_mul UInt64.toBitVec_div UInt64.toBitVec_mod
  UInt64.toBitVec_and UInt64.toBitVec_or UInt64.toBitVec_xor UInt64.toBitVec_shiftLeft UInt64.toBitVec_shiftRight
  UInt64.toBitVec_zero UInt64.toBitVec_one UInt64.toBitVec_not UInt64.toBitVec_neg
  UInt64.eq_iff_toBitVec_eq
  UInt64.toBitVec_ofNat UInt64.toBitVec_ofNat'
  UInt64.toBitVec_toUInt8 UInt64.toBitVec_toUInt16 UInt64.toBitVec_toUInt32 UInt64.toBitVec_toUSize UInt64.toBitVec_toInt64

@[grind hom] theorem Lean.Grind.UInt64.toNat_eq_toBitVec_toNat (x : UInt64) : x.toNat = x.toBitVec.toNat := rfl

/-! Translations of `≤` and `<` into the target domain. -/

attribute [grind hom] UInt64.le_iff_toBitVec_le UInt64.lt_iff_toBitVec_lt
