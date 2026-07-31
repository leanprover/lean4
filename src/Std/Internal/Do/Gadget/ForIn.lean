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

`ForIn.forInWithInvariant` and `ForIn'.forInWithInvariant'` annotate a `forIn`/`forIn'` loop with its
invariant so that `vcgen` reads the invariant from the program. Their `@[spec]` specifications
restate `Spec.forIn_list`/`Spec.forIn'_list` for every container with a `PureForIn` instance.
-/

@[expose] public section

namespace Std.Internal.Do

open Lean.Order

universe u u₁ u₂ v w
variable {α : Type u₁} {β : Type (max u₁ u₂)} {m : Type (max u₁ u₂) → Type v}
  {Pred : Type (max u₁ u₂)} {EPred : Type (max u₁ u₂)}
variable [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]

/-! ## Gadgets -/

set_option linter.unusedVariables false in
/-- A `forIn` loop annotated with its loop invariant, which `vcgen` reads from the `inv` argument.
It is definitionally `forIn xs init f`, so the annotation is erased at runtime. The invariant
ranges over the elements consumed so far, the elements remaining, and the loop state. -/
@[inline] def ForIn.forInWithInvariant {ρ : Type w} [ForIn m ρ α] (xs : ρ) (init : β)
    (f : α → β → m (ForInStep β)) (inv : Invariant α β Pred) : m β :=
  forIn xs init f

set_option linter.unusedVariables false in
/-- A membership-aware `forIn'` loop annotated with its loop invariant, which `vcgen` reads from the
`inv` argument. It is definitionally `forIn' xs init f`, so the annotation is erased at runtime. The
invariant ranges over the elements consumed so far, the elements remaining, and the loop state. -/
@[inline] def ForIn'.forInWithInvariant' {ρ : Type w} {d : Membership α ρ} [ForIn' m ρ α d]
    (xs : ρ) (init : β) (f : (a : α) → a ∈ xs → β → m (ForInStep β))
    (inv : Invariant α β Pred) : m β :=
  forIn' xs init f

/-! ## Specifications -/

@[spec]
theorem Spec.forInWithInvariant {ρ : Type w} [ForIn m ρ α] [ForIn Id ρ α]
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
      (ForIn.forInWithInvariant xs init f inv)
      (inv [] (ForIn.toList xs) init)
      (fun b => inv (ForIn.toList xs) [] b)
      epost := by
  unfold ForIn.forInWithInvariant
  rw [PureForIn.forIn_eq]
  exact Spec.forIn_list inv step

@[spec]
theorem Spec.forInWithInvariant' {ρ : Type w} {d : Membership α ρ} [ForIn' m ρ α d]
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
      (ForIn'.forInWithInvariant' xs init f inv)
      (inv [] (ForIn.toList xs) init)
      (fun b => inv (ForIn.toList xs) [] b)
      epost := by
  unfold ForIn'.forInWithInvariant'
  rw [PureForIn'.forIn'_eq]
  exact Spec.forIn'_list inv step

end Std.Internal.Do
