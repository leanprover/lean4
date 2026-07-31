/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Init.Control.Id
public import Init.Data.List.Control
public import Init.Data.Array.Basic
public import Init.Data.Range.Basic
import Init.Data.Array.Bootstrap
import Init.Data.Array.Lemmas
import Init.Data.List.Basic
import Init.Data.List.Monadic
import Init.Data.List.Range
import Init.Data.Nat.Dvd
import Init.Data.Range.Lemmas
import Init.Omega

/-!
# Deterministic `ForIn` instances

`DeterministicForIn` and `DeterministicForIn'` identify the containers whose loop enumerates the
elements of `ForIn.toList`, and `LawfulMemForIn` transports membership in that list back to the
container. The bridge lemmas compute `ForIn.toList` for each such container.
-/

@[expose] public section

namespace Std.Internal

universe u u₁ v w

/-- Containers whose `Membership` is exactly the elements `ForIn` enumerates. The `Iff` says the
loop yields all members and nothing else; it constrains neither their order nor their multiplicity.
-/
class LawfulMemForIn (ρ : Type w) (α : Type u₁) [d : Membership α ρ] [ForIn Id ρ α] :
    Prop where
  /-- The elements of `ForIn.toList xs` are the members of `xs`. -/
  mem_toList_iff {a : α} {xs : ρ} : a ∈ ForIn.toList xs ↔ a ∈ xs

/-- Containers whose `ForIn` loop is the loop over `ForIn.toList xs`, fixing the order in which
`LawfulMemForIn`'s members are enumerated. -/
class DeterministicForIn (m : Type u → Type v) (ρ : Type w) (α : Type u₁) [Monad m]
    [ForIn m ρ α] [ForIn Id ρ α] : Prop where
  /-- Iterating over `xs` is iterating over `ForIn.toList xs`. -/
  forIn_eq {β : Type u} (xs : ρ) (init : β) (f : α → β → m (ForInStep β)) :
    forIn xs init f = forIn (ForIn.toList xs) init f

/-- Containers whose `ForIn'` loop is the loop over `ForIn.toList xs`. -/
class DeterministicForIn' (m : Type u → Type v) (ρ : Type w) (α : Type u₁) [Monad m]
    {d : Membership α ρ} [ForIn' m ρ α d] [ForIn Id ρ α]
    [LawfulMemForIn ρ α] : Prop where
  /-- Iterating over `xs` is iterating over `ForIn.toList xs`. -/
  forIn'_eq {β : Type u} (xs : ρ) (init : β) (f : (a : α) → a ∈ xs → β → m (ForInStep β)) :
    forIn' xs init f = forIn' (ForIn.toList xs) init fun a h b =>
      f a (LawfulMemForIn.mem_toList_iff.mp h) b

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
  mem_toList_iff {_a _xs} := by rw [ForIn.toList_list]

instance {α : Type u₁} : LawfulMemForIn (Array α) α where
  mem_toList_iff {_a _xs} := by rw [ForIn.toList_array]; exact Array.mem_toList_iff

instance : LawfulMemForIn Std.Legacy.Range Nat where
  mem_toList_iff {a r} := by
    rw [ForIn.toList_range]
    refine ⟨Std.Legacy.Range.mem_of_mem_range', fun h => ?_⟩
    obtain ⟨hlo, hhi, hmod⟩ := h
    have hs := r.step_pos
    have hdvd : (a - r.start) / r.step * r.step = a - r.start :=
      Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hmod)
    rw [List.mem_range']
    refine ⟨(a - r.start) / r.step, ?_, ?_⟩
    · simp only [Std.Legacy.Range.size]
      rw [Nat.div_lt_iff_lt_mul hs]
      have hceil : r.stop - r.start ≤ (r.stop - r.start + r.step - 1) / r.step * r.step := by
        have hdm := Nat.div_add_mod (r.stop - r.start + r.step - 1) r.step
        have hml := Nat.mod_lt (r.stop - r.start + r.step - 1) hs
        rw [Nat.mul_comm] at hdm
        omega
      omega
    · rw [Nat.mul_comm, hdvd]; omega

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

end Std.Internal
