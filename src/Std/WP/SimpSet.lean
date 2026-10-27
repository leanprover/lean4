/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Init.SimpLemmas
public import Init.Data.Nat.Basic

public section

/-!
# The `@[vcgen_simp]` set

`vcgen` rewrites hypotheses, state arguments and verification conditions with the `@[vcgen_simp]`
theorems and with the evaluation of ground terms. This module adds the theorems that remove the
propositional constants `True` and `False`. For example, ground evaluation turns
`"x" = "x" ∨ "x" = "y"` into `True ∨ False`, and `true_or` rewrites that to `True`. It also adds
`Nat.sub_zero`, which removes the `x - 0` that `vcgen +arith` makes from `x + 1 - 1`.
-/

attribute [vcgen_simp] eq_self iff_self
  true_and and_true false_and and_false
  true_or or_true false_or or_false
  not_true_eq_false not_false_eq_true
  true_implies implies_true false_implies
  ite_true ite_false dite_true dite_false
  Nat.sub_zero

end
