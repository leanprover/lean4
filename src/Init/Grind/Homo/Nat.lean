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
public section

/-!
**Note**: the rules in this file are *not* a homomorphism. `Nat` is not a
homomorphism source type (it is not registered in `getHomoSourceTypes`): `grind` has builtin
support for `Nat` in its `cutsat` solver, so there is no injection out of `Nat` and none should
be added. These are support rules for the `BitVec` and `Fin` source types, applied to the `Nat`
images their injections produce: shifts are normalized to arithmetic, `testBit` decomposes
bitwise operations, and the `%`-cleanup rules remove the redundant modular wrappers produced
by the `BitVec.toNat` and `Fin.val` injections.
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
