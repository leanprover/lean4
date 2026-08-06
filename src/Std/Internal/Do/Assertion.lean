/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
module

prelude
public import Init.Internal.Order
public import Std.Internal.Do.Order.Basic
public import Std.Internal.Do.Order.Heyting
public import Std.Internal.Do.Order.Instances
universe u v w
@[expose] public section

set_option linter.missingDocs true

namespace Std.Internal.Do

open Lean.Order
open Std.Internal.Do.CompleteLattice

/-!
# Assertion

The `Assertion` class and lattice capabilities such as total nondeterministic functions.
-/

/-- An assertion type is equipped with a `CompleteLattice` structure,
used as the carrier for pre- and postconditions. -/
class abbrev Assertion (α : Type w) := CompleteLattice α

namespace Assertion

/-!
## Total nondeterministic functions

`CompleteLattice` can embed propositions (`⌜_⌝`) but not values of an arbitrary type `α`.
`NondetFun` equips an assertion lattice with a notion of total nondeterministic functions into
`α`: for a function type `Fun`, an `evalsTo` embedding of the function graph into the lattice,
with a covering law that packs an arbitrary assertion under the graph join. The value type `α`
is an outParam computed from `Pred` and `Fun`, so that elaborating `evalsTo f a` for a
user-written measure `f` determines the type of the pinned value `a`.

The covering law is the *distributed* pack `P ⊑ ⨆ a, evalsTo f a ⊓ P`, which is strictly stronger
than `(⨆ a, evalsTo f a) = ⊤` on a general complete lattice (the latter does not redistribute the
meet into the join). It matches the elim form used by stateful `evalsTo` in the legacy `SPred`
development and avoids an ambient Frame hypothesis at use sites such as `Spec.repeatM`.

The `σ`-indexed instance is `@[reducible]`, so state layers of `evalsTo` peel off by unfolding.
The pure instance is `@[instance_reducible]`: it unfolds during type class resolution and
unification, while the simp and `grind` lemma `evalsTo_pure` rewrites it syntactically.
-/

/--
`Pred` interprets values of `Fun` as total nondeterministic functions into `α`. The value type
`α` is an `outParam` computed from `Pred` and `Fun`.
-/
class NondetFun (Pred : Type u) (Fun : Type u) (α : outParam (Type v)) [Assertion Pred] where
  /-- Relates a nondeterministic function to a value inside the assertion lattice. -/
  evalsTo : Fun → α → Pred
  /-- Every function hits some value: pack `P` under the graph join. -/
  total (f : Fun) (P : Pred) : P ⊑ ⨆ a, evalsTo f a ⊓ P

/-- Pure (state-independent) nondeterministic functions into `α` are just values of `α`.
Low priority so that the `σ`-indexed instance is preferred when both apply. -/
@[instance_reducible] noncomputable instance (priority := low) {Pred : Type u} {α : Type u}
    [Assertion Pred] : NondetFun Pred α α where
  evalsTo f a := ⌜f = a⌝
  total f P := by
    refine le_iSup_of_le f (le_meet _ _ _ ?_ PartialOrder.rel_refl)
    rw [ofProp_eq_top rfl]
    exact le_top P

/-- State-dependent nondeterministic functions: a function for `σ → Pred` is a `σ`-indexed
function for `Pred`. -/
@[reducible] instance {σ : Type u} {Pred : Type u} {Fun : Type u} {α : Type v}
    [Assertion Pred] [inst : NondetFun Pred Fun α] :
    NondetFun (σ → Pred) (σ → Fun) α where
  evalsTo f a := fun s => inst.evalsTo (f s) a
  total f P := by
    intro s
    simpa [iSup_apply, meet_apply] using inst.total (f s) (P s)

@[simp, grind =] theorem NondetFun.evalsTo_pure {Pred : Type u} {α : Type u} [Assertion Pred]
    (f a : α) : NondetFun.evalsTo (Pred := Pred) f a = ⌜f = a⌝ := rfl

/-- Eliminate the covering join of `evalsTo` from the left of an entailment. -/
theorem NondetFun.le_of_total_le {Pred : Type u} {Fun : Type u} {α : Type v}
    [Assertion Pred] [inst : NondetFun Pred Fun α] (f : Fun) {P Q : Pred}
    (h : (⨆ a, inst.evalsTo f a ⊓ P) ⊑ Q) : P ⊑ Q :=
  PartialOrder.rel_trans (inst.total f P) h

end Assertion

end Std.Internal.Do
