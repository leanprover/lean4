/-
Copyright (c) 2026 Andres Erbsen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Erbsen, Leonardo de Moura
-/
module
prelude
import Init.Grind.Attr
public import Init.Data.Nat.Lemmas
public import Init.Data.Nat.Bitwise.Lemmas
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Int.LemmasAux
public import Init.Data.Int.Pow
public import Init.Data.Int.Bitwise.Lemmas
public import Init.Data.Int.DivMod.Bootstrap
public import Init.Data.Int.DivMod.Lemmas
public section

/-!
**Note**: the rules in this file are *not* a homomorphism. `Nat` and `Int` are not
homomorphism source types (they are not registered in `getHomoSourceTypes`): `grind` has
builtin support for both in its `cutsat` solver, including the `Nat` to `Int` cast bridge,
so there is no injection out of `Nat` or `Int` and none should be added. The rules here
support the source types (`BitVec`, `Fin`, the fixed-width integer types), applied to the
`Nat` and `Int` images their injections produce: shifts are normalized to arithmetic,
`testBit` decomposes bitwise operations, and the `%`-cleanup rules remove the redundant
modular wrappers introduced by the injections.
-/

attribute [grind hom]
  Nat.shiftLeft_eq Nat.shiftRight_eq_div_pow
  Nat.mod_add_mod Nat.add_mod_mod Nat.mod_mul_mod Nat.mul_mod_mod Nat.zero_mod
  Nat.testBit_and Nat.testBit_or Nat.testBit_xor
  Nat.testBit_shiftLeft Nat.testBit_shiftRight
  Nat.zero_testBit Nat.testBit_one_eq_true_iff_self_eq_zero
  Nat.testBit_two_pow_sub_one Nat.testBit_mod_two_pow
  Nat.testBit_two_pow_mul

/-
`Nat.testBit_two_pow_mul_add` is intentionally not part of this set: its hypothesis
`a < 2^n` would have to be discharged when the rule is applied, and homomorphism rules
are applied without a discharger. Conditional theorems like this one should be
registered for E-matching instead.
-/

attribute [grind hom]
  Int.shiftLeft_eq Int.shiftRight_eq_div_pow
  Int.ofNat_toNat Int.toNat_sub'
  Int.emod_add_emod Int.add_emod_emod
  Int.emod_sub_emod Int.sub_emod_emod
  Int.emod_emod

@[grind hom] theorem Lean.Grind.Int.emod_mul_emod (m n k : Int) : m % n * k % n = m * k % n := by
  rw [Int.mul_emod, Int.emod_emod, ← Int.mul_emod]

@[grind hom] theorem Lean.Grind.Int.mul_emod_emod (m n k : Int) : m * (n % k) % k = m * n % k := by
  rw [Int.mul_emod, Int.emod_emod, ← Int.mul_emod]
