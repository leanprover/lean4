/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Init.SimpLemmas

public section

/-!
# The `@[vcgen_simp]` set

`vcgen` rewrites hypotheses, state arguments and verification conditions with the `@[vcgen_simp]`
theorems. This module seeds the set with a few theorems about the logical connectives.
-/

attribute [vcgen_simp] eq_self iff_self
  true_and and_true false_and and_false
  true_or or_true false_or or_false
  not_true_eq_false not_false_eq_true
  true_implies implies_true false_implies
  ite_true ite_false dite_true dite_false

end
