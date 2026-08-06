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
`α`: for a function type `Fun`, an `EvalsTo` embedding of the function graph into the lattice,
with a covering law that packs an arbitrary assertion under the graph join. The value type `α`
is an outParam computed from `Pred` and `Fun`, so that elaborating `EvalsTo f a` for a
user-written measure `f` determines the type of the pinned value `a`.

The covering law is the *distributed* pack `P ⊑ ⨆ a, EvalsTo f a ⊓ P`, which is strictly stronger
than `(⨆ a, EvalsTo f a) = ⊤` on a general complete lattice (the latter does not redistribute the
meet into the join). It matches the elim form used by stateful `EvalsTo` in the legacy `SPred`
development.

Both instances are `@[instance_reducible]`: they unfold during type class resolution and
unification, while the simp and `grind` lemmas `evalsTo_pure`, `evalsTo_apply` and its
fixed-arity specializations rewrite them syntactically.
-/

/--
`Pred` interprets values of `Fun` as total nondeterministic functions into `α`. The value type
`α` is an `outParam` computed from `Pred` and `Fun`.
-/
class NondetFun (Pred : Type u) (Fun : Type u) (α : outParam (Type v)) [Assertion Pred] where
  /-- Relates a nondeterministic function to a value inside the assertion lattice. -/
  EvalsTo : Fun → α → Pred
  /-- Every function hits some value: pack `P` under the graph join. -/
  total (f : Fun) (P : Pred) : P ⊑ ⨆ a, EvalsTo f a ⊓ P

/-- Pure (state-independent) nondeterministic functions into `α` are just values of `α`.
Low priority so that the `σ`-indexed instance is preferred when both apply. -/
@[instance_reducible] noncomputable instance (priority := low) {Pred : Type u} {α : Type u}
    [Assertion Pred] : NondetFun Pred α α where
  EvalsTo f a := ⌜f = a⌝
  total f P := by
    refine le_iSup_of_le f (le_meet _ _ _ ?_ PartialOrder.rel_refl)
    rw [ofProp_eq_top rfl]
    exact le_top P

/-- State-dependent nondeterministic functions: a function for `σ → Pred` is a `σ`-indexed
function for `Pred`. -/
@[instance_reducible] instance {σ : Type u} {Pred : Type u} {Fun : Type u} {α : Type v}
    [Assertion Pred] [inst : NondetFun Pred Fun α] :
    NondetFun (σ → Pred) (σ → Fun) α where
  EvalsTo f a := fun s => inst.EvalsTo (f s) a
  total f P := by
    intro s
    simpa [iSup_apply, meet_apply] using inst.total (f s) (P s)

@[simp, grind =] theorem NondetFun.evalsTo_pure {Pred : Type u} {α : Type u} [Assertion Pred]
    (f a : α) : NondetFun.EvalsTo (Pred := Pred) f a = ⌜f = a⌝ := rfl

/-- Pointwise characterization of `EvalsTo` on a function lattice. -/
@[simp] theorem NondetFun.evalsTo_apply {σ : Type u} {Pred : Type u} {Fun : Type u}
    {α : Type v} [Assertion Pred] [NondetFun Pred Fun α] (f : σ → Fun) (a : α) (s : σ) :
    NondetFun.EvalsTo (Pred := σ → Pred) f a s = NondetFun.EvalsTo (f s) a := rfl

/-! `Prop`-valued, fixed-arity specializations of `NondetFun.evalsTo_apply`: the graph of a
state-dependent function at a state-indexed `Prop` lattice, applied to its states, is an
equation. Fixing the carrier to `Prop` (a ground instance) leaves every parameter recoverable
from the trigger, so these are usable `@[grind =]` lemmas where the general `evalsTo_apply` is
not. -/

@[grind =] theorem NondetFun.evalsTo_apply_1 {σ₁ : Type} {α : Type}
    (f : σ₁ → α) (a : α) (s₁ : σ₁) :
    NondetFun.EvalsTo (Pred := σ₁ → Prop) f a s₁ = (f s₁ = a) := by
  simp

@[grind =] theorem NondetFun.evalsTo_apply_2 {σ₁ σ₂ : Type} {α : Type}
    (f : σ₁ → σ₂ → α) (a : α) (s₁ : σ₁) (s₂ : σ₂) :
    NondetFun.EvalsTo (Pred := σ₁ → σ₂ → Prop) f a s₁ s₂ = (f s₁ s₂ = a) := by
  simp

@[grind =] theorem NondetFun.evalsTo_apply_3 {σ₁ σ₂ σ₃ : Type} {α : Type}
    (f : σ₁ → σ₂ → σ₃ → α) (a : α) (s₁ : σ₁) (s₂ : σ₂) (s₃ : σ₃) :
    NondetFun.EvalsTo (Pred := σ₁ → σ₂ → σ₃ → Prop) f a s₁ s₂ s₃ = (f s₁ s₂ s₃ = a) := by
  simp

@[grind =] theorem NondetFun.evalsTo_apply_4 {σ₁ σ₂ σ₃ σ₄ : Type} {α : Type}
    (f : σ₁ → σ₂ → σ₃ → σ₄ → α) (a : α) (s₁ : σ₁) (s₂ : σ₂) (s₃ : σ₃) (s₄ : σ₄) :
    NondetFun.EvalsTo (Pred := σ₁ → σ₂ → σ₃ → σ₄ → Prop) f a s₁ s₂ s₃ s₄
      = (f s₁ s₂ s₃ s₄ = a) := by
  simp

@[grind =] theorem NondetFun.evalsTo_apply_5 {σ₁ σ₂ σ₃ σ₄ σ₅ : Type} {α : Type}
    (f : σ₁ → σ₂ → σ₃ → σ₄ → σ₅ → α) (a : α) (s₁ : σ₁) (s₂ : σ₂) (s₃ : σ₃) (s₄ : σ₄)
    (s₅ : σ₅) :
    NondetFun.EvalsTo (Pred := σ₁ → σ₂ → σ₃ → σ₄ → σ₅ → Prop) f a s₁ s₂ s₃ s₄ s₅
      = (f s₁ s₂ s₃ s₄ s₅ = a) := by
  simp

/-- Eliminate the covering join of `EvalsTo` from the left of an entailment. -/
theorem NondetFun.le_of_total_le {Pred : Type u} {Fun : Type u} {α : Type v}
    [Assertion Pred] [inst : NondetFun Pred Fun α] (f : Fun) {P Q : Pred}
    (h : (⨆ a, inst.EvalsTo f a ⊓ P) ⊑ Q) : P ⊑ Q :=
  PartialOrder.rel_trans (inst.total f P) h

end Assertion

end Std.Internal.Do
