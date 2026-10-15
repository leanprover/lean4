/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Std.WP.Assertion
public import Std.WP.Triple.SpecLemmas

public section

/-!
# Automation for measures

This module registers the automation lemmas of `NondetFun.EvalsTo`, `Variant.EvalsTo` and
`Variant.EvalsBelow` with `simp` and `grind norm`, by the criterion of
`Std.Internal.Order.Automation`. For example, at carrier `Nat → Prop` and the measure
`f := fun (x : Nat × Nat) => (x.1, x.2)`, the decrease `(Variant.ofMeasure f).EvalsBelow (i, j) m s`
rewrites to `i < m.1 ∨ i = m.1 ∧ j < m.2`.
-/

namespace Std.WP

open Assertion

attribute [simp, grind norm] NondetFun.evalsTo_pure NondetFun.evalsTo_apply

attribute [simp, grind norm] Variant.evalsTo_ofMeasure Variant.evalsBelow_ofMeasure_apply
  Variant.evalsBelow_ofMeasure_nat Variant.evalsBelow_ofMeasure_lex

end Std.WP

end
