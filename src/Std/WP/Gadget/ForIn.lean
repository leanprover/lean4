/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Std.WP.Triple.SpecLemmas
public import Std.Internal.ForIn

/-!
# `forIn` loop-invariant gadgets

`forInPureWithInvariant` and `forInPureWithInvariant'` annotate a `forIn`/`forIn'` loop with its
invariant so that `vcgen` reads the invariant from the program. Their `@[spec]` specifications
restate `Spec.forIn_list`/`Spec.forIn'_list` for every container with a `PureForIn` instance.

`forInLoopWithInvariant`, `forInLoopWithVariant` and `forInLoopWithInvariantAndVariant` do the same
for a `repeat` loop, one per set of annotations the loop states. Each restates `Spec.forIn_loop`,
leaving what the loop does not state to `vcgen` to infer.
-/

@[expose] public section

namespace Std.WP

open Lean.Order
open Std.Internal
open Assertion

universe u u₁ u₂ v w
variable {α : Type u₁} {β : Type (max u₁ u₂)} {m : Type (max u₁ u₂) → Type v}
  {Pred : Type (max u₁ u₂)} {EPred : Type (max u₁ u₂)}
variable [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]

/-! ## Gadgets -/

namespace Gadget

set_option linter.unusedVariables false in
/-- A `forIn` loop annotated with its loop invariant, which `vcgen` reads from the `inv` argument.
It is definitionally `forIn xs init f`, so the annotation is erased at runtime. The invariant
ranges over the elements consumed so far, the elements remaining, and the loop state. -/
@[inline] def forInPureWithInvariant {ρ : Type w} [ForIn m ρ α] (xs : ρ) (init : β)
    (f : α → β → m (ForInStep β)) (inv : Invariant α β Pred) : m β :=
  forIn xs init f

set_option linter.unusedVariables false in
/-- A membership-aware `forIn'` loop annotated with its loop invariant, which `vcgen` reads from the
`inv` argument. It is definitionally `forIn' xs init f`, so the annotation is erased at runtime. The
invariant ranges over the elements consumed so far, the elements remaining, and the loop state. -/
@[inline] def forInPureWithInvariant' {ρ : Type w} {d : Membership α ρ} [ForIn' m ρ α d]
    (xs : ρ) (init : β) (f : (a : α) → a ∈ xs → β → m (ForInStep β))
    (inv : Invariant α β Pred) : m β :=
  forIn' xs init f

end Gadget

open Gadget

/-! ## Specifications -/

@[spec]
theorem Spec.forInPure {ρ : Type w} [ForIn m ρ α] [ForIn Id ρ α]
    [PureForIn m ρ α]
    {xs : ρ} {init : β} {f : α → β → m (ForInStep β)}
    (inv : Invariant α β Pred)
    {epost : EPred}
    (step : ∀ pref cur suff (_h : ForIn.toList xs = pref ++ cur :: suff) b,
      Triple
        (f cur b)
        (inv pref (cur :: suff) b)
        (fun r => match r with
          | .yield b' => inv (pref ++ [cur]) suff b'
          | .done b' => inv (ForIn.toList xs) [] b')
        epost) :
    Triple
      (forInPureWithInvariant xs init f inv)
      (inv [] (ForIn.toList xs) init)
      (fun b => inv (ForIn.toList xs) [] b)
      epost := by
  unfold forInPureWithInvariant
  rw [PureForIn.forIn_eq]
  exact Spec.forIn_list inv step

@[spec]
theorem Spec.forInPure' {ρ : Type w} {d : Membership α ρ} [ForIn' m ρ α d]
    [ForIn Id ρ α] [LawfulMemForInId ρ α] [PureForIn' m ρ α]
    {xs : ρ} {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)}
    (inv : Invariant α β Pred)
    {epost : EPred}
    (step : ∀ pref cur suff (h : ForIn.toList xs = pref ++ cur :: suff) b,
      Triple
        (f cur ((LawfulMemForInId.mem_toList_iff).mp (by simp [h])) b)
        (inv pref (cur :: suff) b)
        (fun r => match r with
          | .yield b' => inv (pref ++ [cur]) suff b'
          | .done b' => inv (ForIn.toList xs) [] b')
        epost) :
    Triple
      (forInPureWithInvariant' xs init f inv)
      (inv [] (ForIn.toList xs) init)
      (fun b => inv (ForIn.toList xs) [] b)
      epost := by
  unfold forInPureWithInvariant'
  rw [PureForIn'.forIn'_eq]
  exact Spec.forIn'_list inv step

section Loop

universe uₚ uₑ uq uγ uf

namespace Gadget

set_option linter.unusedVariables false in
/-- A `repeat` loop annotated with the loop invariant that `vcgen` reads from the `inv` argument.
It is definitionally `forIn l init f`, so the annotation is erased at runtime. The invariant ranges
over the loop's cursor, `.inl` while the loop iterates and `.inr` once it is done. -/
@[inline] def forInLoopWithInvariant {β : Type u} {m : Type u → Type v} {Pred : Type uₚ}
    [Monad m] (l : Lean.Loop) (init : β) (f : Unit → β → m (ForInStep β))
    (inv : RepeatInvariant β β Pred) : m β :=
  forIn l init f

set_option linter.unusedVariables false in
/-- A `repeat` loop annotated with the termination measure that `vcgen` reads from the `var`
argument. It is definitionally `forIn l init f`, so the annotation is erased at runtime. The measure
is the function a `RepeatVariant` is built from, so that the assertion language it evaluates in is
the one the specification is applied at. -/
@[inline] def forInLoopWithVariant {β : Type u} {m : Type u → Type v} {Fun : Type}
    [Monad m] (l : Lean.Loop) (init : β) (f : Unit → β → m (ForInStep β))
    (var : β → Fun) : m β :=
  forIn l init f

set_option linter.unusedVariables false in
/-- A `repeat` loop annotated with the loop invariant and the termination measure that `vcgen` reads
from the `inv` and `var` arguments. It is definitionally `forIn l init f`, so the annotations are
erased at runtime. The invariant ranges over the loop's cursor, `.inl` while the loop iterates and
`.inr` once it is done. The measure is the function a `RepeatVariant` is built from, so that the
assertion language it evaluates in is the one the specification is applied at. -/
@[inline] def forInLoopWithInvariantAndVariant {β : Type u} {m : Type u → Type v} {Pred : Type uₚ}
    {Fun : Type} [Monad m] (l : Lean.Loop) (init : β) (f : Unit → β → m (ForInStep β))
    (inv : RepeatInvariant β β Pred) (var : β → Fun) : m β :=
  forIn l init f

end Gadget

variable {β : Type u} {m : Type u → Type v} {Pred : Type uₚ} {EPred : Type uₑ}
variable [Monad m] [Lean.Order.MonadTail m] [Assertion Pred] [Assertion EPred]
  [WPMonad m Pred EPred]

@[spec]
theorem Spec.forInLoop_invariant_variant {Fun : Type} {γ : Type uγ'}
    {l : Lean.Loop} {init : β} {f : Unit → β → m (ForInStep β)}
    [NondetFun Pred Fun γ] [WellFoundedRelation γ] [∀ P : Pred, PreservesSup (meet P)]
    (measure : β → Fun)
    (inv : β ⊕ β → Pred)
    (einv : EPred)
    (step : ∀ b (mb : γ),
      Triple
        (f () b)
        ((RepeatVariant.ofMeasure (Pred := Pred) measure).EvalsTo b mb ⊓ inv (.inl b))
        (fun r => match r with
          | .yield b' =>
            (RepeatVariant.ofMeasure (Pred := Pred) measure).EvalsBelow b' mb ⊓ inv (.inl b')
          | .done b' => inv (.inr b'))
        einv) :
    Triple
      (forInLoopWithInvariantAndVariant l init f (RepeatInvariant.mk inv) measure)
      (inv (.inl init))
      (fun b => inv (.inr b))
      einv := by
  unfold forInLoopWithInvariantAndVariant
  exact Spec.forIn_loop (RepeatVariant.ofMeasure measure) inv einv step

@[spec]
theorem Spec.forInLoop_invariant
    {l : Lean.Loop} {init : β} {f : Unit → β → m (ForInStep β)}
    [∀ P : Pred, PreservesSup (meet P)]
    (measure : RepeatVariant β Pred)
    (inv : β ⊕ β → Pred)
    (einv : EPred)
    (step : ∀ b (mb : measure.γ),
      Triple
        (f () b)
        (measure.EvalsTo b mb ⊓ inv (.inl b))
        (fun r => match r with
          | .yield b' => measure.EvalsBelow b' mb ⊓ inv (.inl b')
          | .done b' => inv (.inr b'))
        einv) :
    Triple
      (forInLoopWithInvariant l init f (RepeatInvariant.mk inv))
      (inv (.inl init))
      (fun b => inv (.inr b))
      einv := by
  unfold forInLoopWithInvariant
  exact Spec.forIn_loop measure inv einv step

@[spec]
theorem Spec.forInLoop_variant {Fun : Type} {γ : Type uγ'}
    {l : Lean.Loop} {init : β} {f : Unit → β → m (ForInStep β)}
    [NondetFun Pred Fun γ] [WellFoundedRelation γ] [∀ P : Pred, PreservesSup (meet P)]
    (measure : β → Fun)
    (inv : RepeatInvariant β β Pred)
    (einv : EPred)
    (step : ∀ b (mb : γ),
      Triple
        (f () b)
        ((RepeatVariant.ofMeasure (Pred := Pred) measure).EvalsTo b mb ⊓ inv (.inl b))
        (fun r => match r with
          | .yield b' =>
            (RepeatVariant.ofMeasure (Pred := Pred) measure).EvalsBelow b' mb ⊓ inv (.inl b')
          | .done b' => inv (.inr b'))
        einv) :
    Triple
      (forInLoopWithVariant l init f measure)
      (inv (.inl init))
      (fun b => inv (.inr b))
      einv := by
  unfold forInLoopWithVariant
  exact Spec.forIn_loop (RepeatVariant.ofMeasure measure) inv einv step

end Loop

end Std.WP
