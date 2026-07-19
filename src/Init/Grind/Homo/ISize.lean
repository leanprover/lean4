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
Homomorphism rules for `ISize` used by the `grind` tactic.
The injection function is `ISize.toBitVec`.
-/

attribute [grind homo]
  ISize.toBitVec_add ISize.toBitVec_sub ISize.toBitVec_mul ISize.toBitVec_div ISize.toBitVec_mod
  ISize.toBitVec_and ISize.toBitVec_or ISize.toBitVec_xor ISize.toBitVec_shiftLeft ISize.toBitVec_shiftRight
  ISize.toBitVec_zero ISize.toBitVec_one ISize.toBitVec_not ISize.toBitVec_neg
  ISize.eq_iff_toBitVec_eq
  ISize.toBitVec_ofNat
  ISize.toBitVec_toInt8 ISize.toBitVec_toInt16 ISize.toBitVec_toInt32 ISize.toBitVec_toInt64 ISize.toBitVec_toUSize

@[grind homo] theorem Lean.Grind.ISize.toInt_eq_toBitVec_toInt (x : ISize) : x.toInt = x.toBitVec.toInt := rfl

/-! Translations of `≤` and `<` into the target domain. -/

attribute [grind homo] ISize.le_iff_toInt_le ISize.lt_iff_toInt_lt
