/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Std.Internal.Do.Triple.SpecLemmas
import Init.Data.Array.Bootstrap
import Init.Data.List.Monadic

/-!
# `forIn` loop-invariant gadgets

`ForIn.forInWithInvariant` and `ForIn'.forInWithInvariant'` annotate a `forIn`/`forIn'` loop with its
invariant so that `vcgen` reads the invariant from the program. The gadgets come first, then the
`@[spec]` specifications that restate `Spec.forIn_list`/`Spec.forIn'_list` for each container.
-/

@[expose] public section

namespace Std.Internal.Do

open Lean.Order

universe u₁ u₂ v w
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
theorem Spec.forInWithInvariant_list
    {xs : List α} {init : β} {f : α → β → m (ForInStep β)}
    (inv : Invariant α β Pred)
    {epost : EPred}
    (step : ∀ pref cur suff (_h : xs = pref ++ cur :: suff) b,
      Triple
        (f cur b)
        (inv pref (cur::suff) b)
        (fun r => match r with
          | .yield b' => inv (pref ++ [cur]) suff b'
          | .done b' => inv xs [] b')
        epost) :
    Triple
      (ForIn.forInWithInvariant xs init f inv)
      (inv [] xs init)
      (fun b => inv xs [] b)
      epost := by
  unfold ForIn.forInWithInvariant
  exact Spec.forIn_list inv step

@[spec]
theorem Spec.forInWithInvariant_range {β : Type u} {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    {xs : Std.Legacy.Range} {init : β} {f : Nat → β → m (ForInStep β)}
    (inv : Invariant Nat β Pred)
    {epost : EPred}
    (step : ∀ pref cur suff (_h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (f cur b)
        (inv pref (cur::suff) b)
        (fun r => match r with
          | .yield b' => inv (pref ++ [cur]) suff b'
          | .done b' => inv xs.toList [] b')
        epost) :
    Triple
      (ForIn.forInWithInvariant xs init f inv)
      (inv [] xs.toList init)
      (fun b => inv xs.toList [] b)
      epost := by
  unfold ForIn.forInWithInvariant
  exact Spec.forIn_range inv step

@[spec]
theorem Spec.forInWithInvariant'_list
    {xs : List α} {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)}
    (inv : Invariant α β Pred)
    {epost : EPred}
    (step : ∀ pref cur suff (h : xs = pref ++ cur :: suff) b,
      Triple
        (f cur (by simp [h]) b)
        (inv pref (cur::suff) b)
        (fun r => match r with
          | .yield b' => inv (pref ++ [cur]) suff b'
          | .done b' => inv xs [] b')
        epost) :
    Triple
      (ForIn'.forInWithInvariant' xs init f inv)
      (inv [] xs init)
      (fun b => inv xs [] b)
      epost := by
  unfold ForIn'.forInWithInvariant'
  exact Spec.forIn'_list inv step

@[spec]
theorem Spec.forInWithInvariant'_range {β : Type u} {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    {xs : Std.Legacy.Range} {init : β} {f : (a : Nat) → a ∈ xs → β → m (ForInStep β)}
    (inv : Invariant Nat β Pred)
    {epost : EPred}
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (f cur (by simp [Std.Legacy.Range.mem_of_mem_range', h]) b)
        (inv pref (cur::suff) b)
        (fun r => match r with
          | .yield b' => inv (pref ++ [cur]) suff b'
          | .done b' => inv xs.toList [] b')
        epost) :
    Triple
      (ForIn'.forInWithInvariant' xs init f inv)
      (inv [] xs.toList init)
      (fun b => inv xs.toList [] b)
      epost := by
  unfold ForIn'.forInWithInvariant'
  exact Spec.forIn'_range inv step

end Std.Internal.Do
