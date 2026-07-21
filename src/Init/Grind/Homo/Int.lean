/-
Copyright (c) 2026 Andres Erbsen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Erbsen, Leonardo de Moura
-/
module
prelude
import Init.Grind.Attr
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Int.LemmasAux
public import Init.Data.Int.Pow
public import Init.Data.Int.Bitwise.Lemmas
public import Init.Data.Int.DivMod.Bootstrap
public import Init.Data.Int.DivMod.Lemmas
public section

/-!
Homomorphism rules for `Int` used by the `grind` tactic.
The `natCast` rules inject `Nat` operations into `Int`, shifts are normalized to
arithmetic, and the `%`-cleanup rules remove redundant modular wrappers produced
by injections into `Int`.
-/

attribute [grind hom]
  Int.natCast_add Int.natCast_mul Int.natCast_pow
  Int.shiftLeft_eq Int.shiftRight_eq_div_pow
  Int.ofNat_toNat Int.toNat_sub'
  Int.emod_add_emod Int.add_emod_emod
  Int.emod_sub_emod Int.sub_emod_emod
  Int.emod_emod

@[grind hom] theorem Lean.Grind.Int.emod_mul_emod (m n k : Int) : m % n * k % n = m * k % n := by
  rw [Int.mul_emod, Int.emod_emod, ← Int.mul_emod]

@[grind hom] theorem Lean.Grind.Int.mul_emod_emod (m n k : Int) : m * (n % k) % k = m * n % k := by
  rw [Int.mul_emod, Int.emod_emod, ← Int.mul_emod]
