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
Homomorphism rules for `UInt8` used by the `grind` tactic.
The injection function is `UInt8.toBitVec`.
-/

attribute [grind homo]
  UInt8.toBitVec_add UInt8.toBitVec_sub UInt8.toBitVec_mul UInt8.toBitVec_div UInt8.toBitVec_mod
  UInt8.toBitVec_and UInt8.toBitVec_or UInt8.toBitVec_xor UInt8.toBitVec_shiftLeft UInt8.toBitVec_shiftRight
  UInt8.toBitVec_zero UInt8.toBitVec_one UInt8.toBitVec_not UInt8.toBitVec_neg
  UInt8.eq_iff_toBitVec_eq
  UInt8.toBitVec_ofNat UInt8.toBitVec_ofNat'
  UInt8.toBitVec_toUInt16 UInt8.toBitVec_toUInt32 UInt8.toBitVec_toUInt64 UInt8.toBitVec_toUSize UInt8.toBitVec_toInt8

@[grind homo] theorem Lean.Grind.UInt8.toNat_eq_toBitVec_toNat (x : UInt8) : x.toNat = x.toBitVec.toNat := rfl

/-! Translations of `≤` and `<` into the target domain. -/

attribute [grind homo] UInt8.le_iff_toBitVec_le UInt8.lt_iff_toBitVec_lt
