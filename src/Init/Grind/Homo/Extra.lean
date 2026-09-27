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
`testBit` decomposes bitwise operations, and the `%`/`bmod`-cleanup rules remove the redundant
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

attribute [grind hom]
  Int.bmod_add_bmod Int.add_bmod_bmod Int.bmod_sub_bmod Int.sub_bmod_bmod
  Int.bmod_mul_bmod Int.mul_bmod_bmod Int.bmod_neg_bmod Int.bmod_bmod
  Int.emod_bmod Int.bmod_emod

@[grind hom] theorem Lean.Grind.Int.emod_mul_emod (m n k : Int) : m % n * k % n = m * k % n := by
  rw [Int.mul_emod, Int.emod_emod, ← Int.mul_emod]

@[grind hom] theorem Lean.Grind.Int.mul_emod_emod (m n k : Int) : m * (n % k) % k = m * n % k := by
  rw [Int.mul_emod, Int.emod_emod, ← Int.mul_emod]

/-!
Support theorems for the builtin `[grind hom]` simproc that rewrites `&&&` with a
literal mask of the form `1…10…0` over `Nat`. The simproc instantiates `n` and `k`
from the mask, and the hypotheses are discharged by `rfl` (the kernel evaluates the
powers). The results use `%`, `/`, and `*` by literals, which `cutsat` supports.
-/

theorem Lean.Grind.Nat.and_eq_mod (x c m n : Nat) (h₁ : c = 2^n - 1) (h₂ : m = 2^n) :
    x &&& c = x % m := by
  subst h₁ h₂; exact Nat.and_two_pow_sub_one_eq_mod x n

theorem Lean.Grind.Nat.ones_and_eq_mod (x c m n : Nat) (h₁ : c = 2^n - 1) (h₂ : m = 2^n) :
    c &&& x = x % m := by
  rw [Nat.and_comm]; exact and_eq_mod x c m n h₁ h₂

theorem Lean.Grind.Nat.and_eq_div_mod_mul (x c p q k n : Nat)
    (h₁ : c = (2^n - 1) * 2^k) (h₂ : p = 2^k) (h₃ : q = 2^n) :
    x &&& c = x / p % q * p := by
  subst h₁ h₂ h₃
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_mul_two_pow, Nat.testBit_two_pow_sub_one,
    Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  cases Nat.lt_or_ge i k with
  | inl h => simp [Nat.not_le_of_lt h]
  | inr h => simp [h, Nat.sub_add_cancel h, Bool.and_comm]

theorem Lean.Grind.Nat.ones_zeros_and_eq_div_mod_mul (x c p q k n : Nat)
    (h₁ : c = (2^n - 1) * 2^k) (h₂ : p = 2^k) (h₃ : q = 2^n) :
    c &&& x = x / p % q * p := by
  rw [Nat.and_comm]; exact and_eq_div_mod_mul x c p q k n h₁ h₂ h₃
