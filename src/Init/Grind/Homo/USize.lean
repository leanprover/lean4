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
Homomorphism rules for `USize` used by the `grind` tactic.
The injection function is `USize.toBitVec`.
-/

attribute [grind hom]
  USize.toBitVec_add USize.toBitVec_sub USize.toBitVec_mul USize.toBitVec_div USize.toBitVec_mod
  USize.toBitVec_and USize.toBitVec_or USize.toBitVec_xor USize.toBitVec_shiftLeft USize.toBitVec_shiftRight
  USize.toBitVec_zero USize.toBitVec_one USize.toBitVec_not USize.toBitVec_neg
  USize.eq_iff_toBitVec_eq
  USize.toBitVec_ofNat USize.toBitVec_ofNat'
  USize.toBitVec_toUInt8 USize.toBitVec_toUInt16 USize.toBitVec_toUInt32 USize.toBitVec_toUInt64 USize.toBitVec_toISize

@[grind hom] theorem Lean.Grind.USize.toNat_eq_toBitVec_toNat (x : USize) : x.toNat = x.toBitVec.toNat := rfl

/-! Translations of `≤` and `<` into the target domain. -/

attribute [grind hom] USize.le_iff_toBitVec_le USize.lt_iff_toBitVec_lt
