/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Std.Internal.Do.Triple.SpecLemmas
public import Std.Internal.ForIn

/-!
# `forIn` loop-invariant gadgets

`forInPureWithInvariant` and `forInPureWithInvariant'` annotate a `forIn`/`forIn'` loop with its
invariant so that `vcgen` reads the invariant from the program. Their `@[spec]` specifications
restate `Spec.forIn_list`/`Spec.forIn'_list` for every container with a `PureForIn` instance.

`forInLoopWithInvariantAndVariant` does the same for a `repeat` loop, carrying an invariant and a
termination measure, either of which may be absent. Its specifications restate `Spec.forIn_loop`,
one per combination a loop annotation produces, leaving an absent annotation to `vcgen` to infer.
-/

@[expose] public section

namespace Std.Internal.Do

open Lean.Order
open Assertion

universe u u₁ u₂ v w
variable {α : Type u₁} {β : Type (max u₁ u₂)} {m : Type (max u₁ u₂) → Type v}
  {Pred : Type (max u₁ u₂)} {EPred : Type (max u₁ u₂)}
variable [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]

/-! ## Gadgets -/

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

set_option linter.unusedVariables false in
/-- A `repeat` loop annotated with the loop invariant and the termination measure that `vcgen` reads
from the `inv?` and `var?` arguments. It is definitionally `forIn l init f`, so the annotations are
erased at runtime. The invariant ranges over the loop's cursor, `.inl` while the loop iterates and
`.inr` once it is done. The measure is the function a `RepeatVariant` is built from, so that the
assertion language it evaluates in is the one the specification is applied at. -/
@[inline] def forInLoopWithInvariantAndVariant {β : Type u} {m : Type u → Type v} {Pred : Type uₚ}
    {Fun : Type uf} [Monad m] (l : Lean.Loop) (init : β) (f : Unit → β → m (ForInStep β))
    (inv? : Option (RepeatInvariant β β Pred)) (var? : Option (β → Fun)) : m β :=
  forIn l init f

variable {β : Type u} {m : Type u → Type v} {Pred : Type uₚ} {EPred : Type uₑ}
variable [Monad m] [Lean.Order.MonadTail m] [Assertion Pred] [Assertion EPred]
  [WPMonad m Pred EPred]

@[spec]
theorem Spec.forInLoop_invariant_variant
    {l : Lean.Loop} {init : β} {f : Unit → β → m (ForInStep β)}
    [∀ P : Pred, PreservesSup (meet P)]
    (measure : β → Nat)
    (inv : RepeatInvariant β β Pred)
    (einv : EPred)
    (step : ∀ b (mb : Nat),
      Triple
        (f () b)
        ((RepeatVariant.ofMeasure (Pred := Pred) measure).EvalsTo b mb ⊓ inv (.inl b))
        (fun r => match r with
          | .yield b' =>
            (RepeatVariant.ofMeasure (Pred := Pred) measure).EvalsBelow b' mb ⊓ inv (.inl b')
          | .done b' => inv (.inr b'))
        einv) :
    Triple
      (forInLoopWithInvariantAndVariant l init f (some inv) (some measure))
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
    (inv : RepeatInvariant β β Pred)
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
      (forInLoopWithInvariantAndVariant l init f (some inv) (none : Option (β → Unit)))
      (inv (.inl init))
      (fun b => inv (.inr b))
      einv := by
  unfold forInLoopWithInvariantAndVariant
  exact Spec.forIn_loop measure inv einv step

@[spec]
theorem Spec.forInLoop_variant
    {l : Lean.Loop} {init : β} {f : Unit → β → m (ForInStep β)}
    [∀ P : Pred, PreservesSup (meet P)]
    (measure : β → Nat)
    (inv : RepeatInvariant β β Pred)
    (einv : EPred)
    (step : ∀ b (mb : Nat),
      Triple
        (f () b)
        ((RepeatVariant.ofMeasure (Pred := Pred) measure).EvalsTo b mb ⊓ inv (.inl b))
        (fun r => match r with
          | .yield b' =>
            (RepeatVariant.ofMeasure (Pred := Pred) measure).EvalsBelow b' mb ⊓ inv (.inl b')
          | .done b' => inv (.inr b'))
        einv) :
    Triple
      (forInLoopWithInvariantAndVariant (Pred := Prop) l init f none (some measure))
      (inv (.inl init))
      (fun b => inv (.inr b))
      einv := by
  unfold forInLoopWithInvariantAndVariant
  exact Spec.forIn_loop (RepeatVariant.ofMeasure measure) inv einv step

end Loop

end Std.Internal.Do
