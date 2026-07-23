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
ranges over the loop's iteration cursor, viewed through `ForIn.toList`. -/
@[inline] def ForIn.forInWithInvariant {ρ : Type w} [ForIn m ρ α] [ForIn Id ρ α] (xs : ρ) (init : β)
    (f : α → β → m (ForInStep β)) (inv : Invariant (ForIn.toList xs) β Pred) : m β :=
  forIn xs init f

set_option linter.unusedVariables false in
/-- A membership-aware `forIn'` loop annotated with its loop invariant, which `vcgen` reads from the
`inv` argument. It is definitionally `forIn' xs init f`, so the annotation is erased at runtime. The
invariant ranges over the loop's iteration cursor, viewed through `ForIn.toList`. -/
@[inline] def ForIn'.forInWithInvariant' {ρ : Type w} {d : Membership α ρ} [ForIn' m ρ α d]
    [ForIn Id ρ α] (xs : ρ) (init : β) (f : (a : α) → a ∈ xs → β → m (ForInStep β))
    (inv : Invariant (ForIn.toList xs) β Pred) : m β :=
  forIn' xs init f

/-! ## Bridge lemmas

`ForIn.toList xs` unfolds to the concrete list of each container, so the specifications below can
present their cursors over that concrete list and keep `ForIn.toList` out of the verification
conditions. -/

private theorem foldl_push_toList {γ : Type u₁} (xs : List γ) (acc : Array γ) :
    (xs.foldl (fun acc a => acc.push a) acc).toList = acc.toList ++ xs := by
  induction xs generalizing acc with
  | nil => simp
  | cons a xs ih => rw [List.foldl_cons, ih, Array.toList_push]; simp

theorem ForIn.toList_list {γ : Type u₁} (xs : List γ) : ForIn.toList xs = xs := by
  simp only [ForIn.toList, ForIn.toArray, Id.run, List.forIn_pure_yield_eq_foldl]
  change (List.foldl (fun acc a => acc.push a) #[] xs).toList = xs
  rw [foldl_push_toList]; simp

theorem ForIn.toList_range (r : Std.Legacy.Range) : ForIn.toList r = r.toList := by
  simp only [ForIn.toList, ForIn.toArray, Id.run, Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl]
  change (List.foldl (fun acc a => acc.push a) #[]
    (List.range' r.start r.size r.step)).toList = r.toList
  rw [foldl_push_toList]; simp [Std.Legacy.Range.toList, Std.Legacy.Range.size]

/-! ## Specifications -/

@[spec]
theorem Spec.forInWithInvariant_list
    {xs : List α} {init : β} {f : α → β → m (ForInStep β)}
    (inv : Invariant (ForIn.toList xs) β Pred)
    {epost : EPred}
    (step : ∀ pref cur suff (h : xs = pref ++ cur :: suff) b,
      Triple
        (f cur b)
        (inv ⟨pref, cur::suff, by simp [ForIn.toList_list, h]⟩ b)
        (fun r => match r with
          | .yield b' => inv ⟨pref ++ [cur], suff, by simp [ForIn.toList_list, h]⟩ b'
          | .done b' => inv ⟨xs, [], by simp [ForIn.toList_list]⟩ b')
        epost) :
    Triple
      (ForIn.forInWithInvariant xs init f inv)
      (inv ⟨[], xs, by simp [ForIn.toList_list]⟩ init)
      (fun b => inv ⟨xs, [], by simp [ForIn.toList_list]⟩ b)
      epost := by
  have key : ForIn.toList xs = xs := ForIn.toList_list xs
  unfold ForIn.forInWithInvariant
  exact Spec.forIn_list (inv := fun c b => inv (c.cast key.symm) b) step

@[spec]
theorem Spec.forInWithInvariant_range {β : Type u} {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    {xs : Std.Legacy.Range} {init : β} {f : Nat → β → m (ForInStep β)}
    (inv : Invariant (ForIn.toList xs) β Pred)
    {epost : EPred}
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (f cur b)
        (inv ⟨pref, cur::suff, by simp [ForIn.toList_range, h]⟩ b)
        (fun r => match r with
          | .yield b' => inv ⟨pref ++ [cur], suff, by simp [ForIn.toList_range, h]⟩ b'
          | .done b' => inv ⟨xs.toList, [], by simp [ForIn.toList_range]⟩ b')
        epost) :
    Triple
      (ForIn.forInWithInvariant xs init f inv)
      (inv ⟨[], xs.toList, by simp [ForIn.toList_range]⟩ init)
      (fun b => inv ⟨xs.toList, [], by simp [ForIn.toList_range]⟩ b)
      epost := by
  have key : ForIn.toList xs = xs.toList := ForIn.toList_range xs
  unfold ForIn.forInWithInvariant
  rw [show (forIn xs init f : m β) = forIn xs.toList init f by
    simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.toList, Std.Legacy.Range.size]]
  exact Spec.forIn_list (inv := fun c b => inv (c.cast key.symm) b) step

@[spec]
theorem Spec.forInWithInvariant'_list
    {xs : List α} {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)}
    (inv : Invariant (ForIn.toList xs) β Pred)
    {epost : EPred}
    (step : ∀ pref cur suff (h : xs = pref ++ cur :: suff) b,
      Triple
        (f cur (by simp [h]) b)
        (inv ⟨pref, cur::suff, by simp [ForIn.toList_list, h]⟩ b)
        (fun r => match r with
          | .yield b' => inv ⟨pref ++ [cur], suff, by simp [ForIn.toList_list, h]⟩ b'
          | .done b' => inv ⟨xs, [], by simp [ForIn.toList_list]⟩ b')
        epost) :
    Triple
      (ForIn'.forInWithInvariant' xs init f inv)
      (inv ⟨[], xs, by simp [ForIn.toList_list]⟩ init)
      (fun b => inv ⟨xs, [], by simp [ForIn.toList_list]⟩ b)
      epost := by
  have key : ForIn.toList xs = xs := ForIn.toList_list xs
  unfold ForIn'.forInWithInvariant'
  exact Spec.forIn'_list (inv := fun c b => inv (c.cast key.symm) b) step

@[spec]
theorem Spec.forInWithInvariant'_range {β : Type u} {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    {xs : Std.Legacy.Range} {init : β} {f : (a : Nat) → a ∈ xs → β → m (ForInStep β)}
    (inv : Invariant (ForIn.toList xs) β Pred)
    {epost : EPred}
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (f cur (by simp [Std.Legacy.Range.mem_of_mem_range', h]) b)
        (inv ⟨pref, cur::suff, by simp [ForIn.toList_range, h]⟩ b)
        (fun r => match r with
          | .yield b' => inv ⟨pref ++ [cur], suff, by simp [ForIn.toList_range, h]⟩ b'
          | .done b' => inv ⟨xs.toList, [], by simp [ForIn.toList_range]⟩ b')
        epost) :
    Triple
      (ForIn'.forInWithInvariant' xs init f inv)
      (inv ⟨[], xs.toList, by simp [ForIn.toList_range]⟩ init)
      (fun b => inv ⟨xs.toList, [], by simp [ForIn.toList_range]⟩ b)
      epost := by
  have key : ForIn.toList xs = xs.toList := ForIn.toList_range xs
  unfold ForIn'.forInWithInvariant'
  exact Spec.forIn'_range (inv := fun c b => inv (c.cast key.symm) b) step

end Std.Internal.Do
