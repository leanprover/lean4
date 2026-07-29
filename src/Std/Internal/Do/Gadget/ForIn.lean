/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Std.Internal.Do.Triple.SpecLemmas
import Init.Data.Array.Bootstrap
import Init.Data.Array.Lemmas
import Init.Data.List.Monadic

/-!
# `forIn` loop-invariant gadgets

`ForIn.forInWithInvariant` and `ForIn'.forInWithInvariant'` annotate a `forIn`/`forIn'` loop with its
invariant so that `vcgen` reads the invariant from the program. The gadgets come first, then the
classes `DeterministicForIn`/`DeterministicForIn'` identifying the containers that enumerate the
elements of `ForIn.toList` and the membership transport `LawfulMemForIn`, and finally the `@[spec]`
specifications that restate `Spec.forIn_list`/`Spec.forIn'_list` for every such container.
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

/-! ## Deterministic iteration -/

/-- Containers whose `ForIn` loop is the loop over `ForIn.toList xs`. -/
class DeterministicForIn (m : Type u → Type v) (ρ : Type w) (α : Type u₁) [Monad m]
    [ForIn m ρ α] [ForIn Id ρ α] : Prop where
  /-- Iterating over `xs` is iterating over `ForIn.toList xs`. -/
  forIn_eq {β : Type u} (xs : ρ) (init : β) (f : α → β → m (ForInStep β)) :
    forIn xs init f = forIn (ForIn.toList xs) init f

/-- Containers whose `Membership` agrees with the elements `ForIn` enumerates. -/
class LawfulMemForIn (ρ : Type w) (α : Type u₁) [d : Membership α ρ] [ForIn Id ρ α] :
    Prop where
  /-- Every element of `ForIn.toList xs` is a member of `xs`. -/
  mem_of_mem_toList {a : α} {xs : ρ} : a ∈ ForIn.toList xs → a ∈ xs

/-- Containers whose `ForIn'` loop is the loop over `ForIn.toList xs`. -/
class DeterministicForIn' (m : Type u → Type v) (ρ : Type w) (α : Type u₁) [Monad m]
    {d : Membership α ρ} [ForIn' m ρ α d] [ForIn Id ρ α]
    [LawfulMemForIn ρ α] : Prop where
  /-- Iterating over `xs` is iterating over `ForIn.toList xs`. -/
  forIn'_eq {β : Type u} (xs : ρ) (init : β) (f : (a : α) → a ∈ xs → β → m (ForInStep β)) :
    forIn' xs init f = forIn' (ForIn.toList xs) init fun a h b =>
      f a (LawfulMemForIn.mem_of_mem_toList h) b

/-! ## Bridge lemmas

`ForIn.toList xs` computes the concrete list of each container, in the spelling that carries the
membership lemmas the verification conditions need. -/

private theorem foldl_push_toList {γ : Type u₁} (xs : List γ) (acc : Array γ) :
    (xs.foldl (fun acc a => acc.push a) acc).toList = acc.toList ++ xs := by
  induction xs generalizing acc with
  | nil => simp
  | cons a xs ih => rw [List.foldl_cons, ih, Array.toList_push]; simp

@[simp, grind =] theorem ForIn.toList_list {γ : Type u₁} (xs : List γ) : ForIn.toList xs = xs := by
  simp only [ForIn.toList, ForIn.toArray, Id.run, List.forIn_pure_yield_eq_foldl]
  change (List.foldl (fun acc a => acc.push a) #[] xs).toList = xs
  rw [foldl_push_toList]; simp

@[simp, grind =] theorem ForIn.toList_array {γ : Type u₁} (xs : Array γ) :
    ForIn.toList xs = xs.toList := by
  simp only [ForIn.toList, ForIn.toArray, Id.run, ← Array.forIn_toList,
    List.forIn_pure_yield_eq_foldl]
  change (List.foldl (fun acc a => acc.push a) #[] xs.toList).toList = xs.toList
  rw [foldl_push_toList]; simp

@[simp, grind =] theorem ForIn.toList_range (r : Std.Legacy.Range) :
    ForIn.toList r = List.range' r.start r.size r.step := by
  simp only [ForIn.toList, ForIn.toArray, Id.run, Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl]
  change (List.foldl (fun acc a => acc.push a) #[]
    (List.range' r.start r.size r.step)).toList = _
  rw [foldl_push_toList]; simp

/-! ## Instances -/

private theorem forIn'_cast {γ : Type u₁} {δ : Type u} {n : Type u → Type v} [Monad n]
    {l l' : List γ} (hl : l = l') (init : δ) (f : (a : γ) → a ∈ l' → δ → n (ForInStep δ)) :
    forIn' l init (fun a ha b => f a (hl ▸ ha) b) = forIn' l' init f :=
  List.forIn'_congr hl rfl fun _ _ _ => rfl

instance {m : Type u → Type v} [Monad m] {α : Type u₁} : DeterministicForIn m (List α) α where
  forIn_eq xs init f := by rw [ForIn.toList_list]

instance {m : Type u → Type v} [Monad m] {α : Type u₁} : DeterministicForIn m (Array α) α where
  forIn_eq xs init f := by rw [ForIn.toList_array, Array.forIn_toList]

instance {m : Type u → Type v} [Monad m] : DeterministicForIn m Std.Legacy.Range Nat where
  forIn_eq r init f := by
    rw [ForIn.toList_range]; exact Std.Legacy.Range.forIn_eq_forIn_range' ..

instance {α : Type u₁} : LawfulMemForIn (List α) α where
  mem_of_mem_toList h := by rwa [ForIn.toList_list] at h

instance {α : Type u₁} : LawfulMemForIn (Array α) α where
  mem_of_mem_toList h := Array.mem_toList_iff.mp (by rwa [ForIn.toList_array] at h)

instance : LawfulMemForIn Std.Legacy.Range Nat where
  mem_of_mem_toList h := Std.Legacy.Range.mem_of_mem_range' (by rwa [ForIn.toList_range] at h)

instance {m : Type u → Type v} [Monad m] {α : Type u₁} : DeterministicForIn' m (List α) α where
  forIn'_eq xs init f := (forIn'_cast (ForIn.toList_list xs) init f).symm

instance {m : Type u → Type v} [Monad m] {α : Type u₁} : DeterministicForIn' m (Array α) α where
  forIn'_eq xs init f :=
    ((forIn'_cast (ForIn.toList_array xs) init
      (fun a ha b => f a (Array.mem_toList_iff.mp ha) b)).trans Array.forIn'_toList).symm

instance {m : Type u → Type v} [Monad m] : DeterministicForIn' m Std.Legacy.Range Nat where
  forIn'_eq r init f := by
    rw [Std.Legacy.Range.forIn'_eq_forIn'_range']
    exact (forIn'_cast (ForIn.toList_range r) init
      (fun a ha b => f a (Std.Legacy.Range.mem_of_mem_range' ha) b)).symm

/-! ## Specifications -/

@[spec]
theorem Spec.forInWithInvariant_det {ρ : Type w} [ForIn m ρ α] [ForIn Id ρ α]
    [DeterministicForIn m ρ α]
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
  rw [DeterministicForIn.forIn_eq]
  exact Spec.forIn_list inv step

@[spec]
theorem Spec.forInWithInvariant'_det {ρ : Type w} {d : Membership α ρ} [ForIn' m ρ α d]
    [ForIn Id ρ α] [LawfulMemForIn ρ α] [DeterministicForIn' m ρ α]
    {xs : ρ} {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)}
    (inv : Invariant α β Pred)
    {epost : EPred}
    (step : ∀ pref cur suff (h : ForIn.toList xs = pref ++ cur :: suff) b,
      Triple
        (f cur (LawfulMemForIn.mem_of_mem_toList (by simp [h])) b)
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
  rw [DeterministicForIn'.forIn'_eq]
  exact Spec.forIn'_list inv step

end Std.Internal.Do
