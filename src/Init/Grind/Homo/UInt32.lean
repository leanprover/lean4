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
Homomorphism rules for `UInt32` used by the `grind` tactic.
The injection function is `UInt32.toBitVec`.
-/

attribute [grind hom]
  UInt32.toBitVec_add UInt32.toBitVec_sub UInt32.toBitVec_mul UInt32.toBitVec_div UInt32.toBitVec_mod
  UInt32.toBitVec_and UInt32.toBitVec_or UInt32.toBitVec_xor UInt32.toBitVec_shiftLeft UInt32.toBitVec_shiftRight
  UInt32.toBitVec_zero UInt32.toBitVec_one UInt32.toBitVec_not UInt32.toBitVec_neg
  UInt32.eq_iff_toBitVec_eq
  UInt32.toBitVec_toUInt8 UInt32.toBitVec_toUInt16 UInt32.toBitVec_toUInt64 UInt32.toBitVec_toUSize UInt32.toBitVec_toInt32


/- The core `UInt32.toBitVec_ofNat` rules produce literals in `BitVec.ofNat` form; `grind`
keeps `BitVec` literals in `OfNat.ofNat` form, so they are restated with a canonical
right-hand side. -/
@[grind hom] theorem Lean.Grind.UInt32.toBitVec_OfNat_ofNat (a : Nat) :
    (OfNat.ofNat a : UInt32).toBitVec = OfNat.ofNat a :=
  (UInt32.toBitVec_ofNat a).trans BitVec.ofNat_eq_ofNat.symm

@[grind hom] theorem Lean.Grind.UInt32.toBitVec_ofNat (a : Nat) :
    (UInt32.ofNat a).toBitVec = OfNat.ofNat a :=
  (UInt32.toBitVec_ofNat' a).trans BitVec.ofNat_eq_ofNat.symm

@[grind hom] theorem Lean.Grind.UInt32.toNat_eq_toBitVec_toNat (x : UInt32) : x.toNat = x.toBitVec.toNat := rfl

/-! Translations of `≤` and `<` into the target domain. -/

attribute [grind hom] UInt32.le_iff_toBitVec_le UInt32.lt_iff_toBitVec_lt
