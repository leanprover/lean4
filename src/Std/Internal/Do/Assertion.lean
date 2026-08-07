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
universe u v w s
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
`NondetFun Pred Fun α` equips an assertion lattice `Pred` with a notion of total
nondeterministic functions `Fun` into `α`. For example, at `Pred = Nat → Prop` the instances
are set up such that `Fun := Nat → α`, a function reading the `Nat` state. The assertion
`EvalsTo f a` states that `f` evaluates to the value `a`; in the example it is
`fun s => ⌜f s = a⌝`. The law `total` states that `f` evaluates to some value:
`(⨆ a, EvalsTo f a) = ⊤`. The value type `α` is the `outParam` because instances are
synthesized while only the function `f` is at hand: resolution knows `Pred` and `Fun` and
computes `α`, whose values first occur in the assertions the instance builds.
-/

/--
`Pred` interprets values of `Fun` as total nondeterministic functions into `α`. The value type
`α` is an `outParam` computed from `Pred` and `Fun`.
-/
class NondetFun (Pred : Type u) (Fun : Type v) (α : outParam (Type w)) [Assertion Pred] where
  /-- Relates a nondeterministic function to a value inside the assertion lattice. -/
  EvalsTo : Fun → α → Pred
  /-- Every function hits some value. -/
  total (f : Fun) : (⨆ a, EvalsTo f a) = ⊤

/-- Pure (state-independent) nondeterministic functions into `α` are just values of `α`.
Low priority so that the `σ`-indexed instance is preferred when both apply. -/
noncomputable instance (priority := low) {Pred : Type u} {α : Type v}
    [Assertion Pred] : NondetFun Pred α α where
  EvalsTo f a := ⌜f = a⌝
  total f := PartialOrder.rel_antisymm (le_top _) (le_iSup_of_le f (le_ofProp _ _ rfl))

/-- State-dependent nondeterministic functions: a function for `σ → Pred` is a `σ`-indexed
function for `Pred`. -/
instance {σ : Type s} {Pred : Type u} {Fun : Type v} {α : Type w}
    [Assertion Pred] [inst : NondetFun Pred Fun α] :
    NondetFun (σ → Pred) (σ → Fun) α where
  EvalsTo f a := fun s => inst.EvalsTo (f s) a
  total f := by
    funext s
    simpa [iSup_apply, top_apply] using inst.total (f s)

@[simp, grind =] theorem NondetFun.evalsTo_pure {Pred : Type u} {α : Type v} [Assertion Pred]
    (f a : α) : NondetFun.EvalsTo (Pred := Pred) f a = ⌜f = a⌝ := rfl

/-- Pointwise characterization of `EvalsTo` on a function lattice. -/
@[simp] theorem NondetFun.evalsTo_apply {σ : Type s} {Pred : Type u} {Fun : Type v}
    {α : Type w} [Assertion Pred] [NondetFun Pred Fun α] (f : σ → Fun) (a : α) (s : σ) :
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
theorem NondetFun.le_of_total_le {Pred : Type u} {Fun : Type v} {α : Type w}
    [Assertion Pred] [inst : NondetFun Pred Fun α] (f : Fun) {P Q : Pred}
    [PreservesSup (meet P)]
    (h : (⨆ a, inst.EvalsTo f a ⊓ P) ⊑ Q) : P ⊑ Q := by
  have h1 : P ⊑ (⨆ a, inst.EvalsTo f a) ⊓ P := by
    rw [inst.total f, top_meet]
  have h2 : (⨆ a, inst.EvalsTo f a) ⊓ P ⊑ ⨆ a, inst.EvalsTo f a ⊓ P :=
    iSup_meet_le fun a => le_iSup (fun a => inst.EvalsTo f a ⊓ P) a
  exact PartialOrder.rel_trans h1 (PartialOrder.rel_trans h2 h)

end Assertion

end Std.Internal.Do
