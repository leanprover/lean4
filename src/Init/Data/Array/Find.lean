/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.List.Find
import Init.Data.Array.Lemmas
import Init.Data.Array.Attach

/-!
# Lemmas about `Array.findSome?`, `Array.find?`.
-/

namespace Array

open Nat

/-! ### findSome? -/

@[simp] theorem findSomeRev?_push_of_isSome (l : Array α) (h : (f a).isSome) : (l.push a).findSomeRev? f = f a := by
  cases l; simp_all

@[simp] theorem findSomeRev?_push_of_isNone (l : Array α) (h : (f a).isNone) : (l.push a).findSomeRev? f = l.findSomeRev? f := by
  cases l; simp_all

theorem exists_of_findSome?_eq_some {f : α → Option β} {l : Array α} (w : l.findSome? f = some b) :
    ∃ a, a ∈ l ∧ f a = b := by
  cases l; simp_all [List.exists_of_findSome?_eq_some]

@[simp] theorem findSome?_eq_none_iff : findSome? p l = none ↔ ∀ x ∈ l, p x = none := by
  cases l; simp

@[simp] theorem findSome?_isSome_iff {f : α → Option β} {l : Array α} :
    (l.findSome? f).isSome ↔ ∃ x, x ∈ l ∧ (f x).isSome := by
  cases l; simp

theorem findSome?_eq_some_iff {f : α → Option β} {l : Array α} {b : β} :
    l.findSome? f = some b ↔ ∃ (l₁ : Array α) (a : α) (l₂ : Array α), l = l₁.push a ++ l₂ ∧ f a = some b ∧ ∀ x ∈ l₁, f x = none := by
  cases l
  simp only [List.findSome?_toArray, List.findSome?_eq_some_iff]
  constructor
  · rintro ⟨l₁, a, l₂, rfl, h₁, h₂⟩
    exact ⟨l₁.toArray, a, l₂.toArray, by simp_all⟩
  · rintro ⟨l₁, a, l₂, h₀, h₁, h₂⟩
    exact ⟨l₁.toList, a, l₂.toList, by simpa using congrArg toList h₀, h₁, by simpa⟩

@[simp] theorem findSome?_guard (l : Array α) : findSome? (Option.guard fun x => p x) l = find? p l := by
  cases l; simp

@[simp] theorem getElem?_zero_filterMap (f : α → Option β) (l : Array α) : (l.filterMap f)[0]? = l.findSome? f := by
  cases l; simp [← List.head?_eq_getElem?]

@[simp] theorem getElem_zero_filterMap (f : α → Option β) (l : Array α) (h) :
    (l.filterMap f)[0] = (l.findSome? f).get (by cases l; simpa [List.length_filterMap_eq_countP] using h) := by
  cases l; simp [← List.head_eq_getElem, ← getElem?_zero_filterMap]

@[simp] theorem back?_filterMap (f : α → Option β) (l : Array α) : (l.filterMap f).back? = l.findSomeRev? f := by
  cases l; simp

@[simp] theorem back!_filterMap [Inhabited β] (f : α → Option β) (l : Array α) :
    (l.filterMap f).back! = (l.findSomeRev? f).getD default := by
  cases l; simp

@[simp] theorem map_findSome? (f : α → Option β) (g : β → γ) (l : Array α) :
    (l.findSome? f).map g = l.findSome? (Option.map g ∘ f) := by
  cases l; simp

theorem findSome?_map (f : β → γ) (l : Array β) : findSome? p (l.map f) = l.findSome? (p ∘ f) := by
  cases l; simp [List.findSome?_map]

theorem findSome?_append {l₁ l₂ : Array α} : (l₁ ++ l₂).findSome? f = (l₁.findSome? f).or (l₂.findSome? f) := by
  cases l₁; cases l₂; simp [List.findSome?_append]

theorem getElem?_zero_flatten (L : Array (Array α)) :
    (flatten L)[0]? = L.findSome? fun l => l[0]? := by
  cases L using array_array_induction
  simp [← List.head?_eq_getElem?, List.head?_flatten, List.findSome?_map, Function.comp_def]

theorem getElem_zero_flatten.proof {L : Array (Array α)} (h : 0 < L.flatten.size) :
    (L.findSome? fun l => l[0]?).isSome := by
  cases L using array_array_induction
  simp only [List.findSome?_toArray, List.findSome?_map, Function.comp_def, List.getElem?_toArray,
    List.findSome?_isSome_iff, List.isSome_getElem?]
  simp only [flatten_toArray_map_toArray, size_toArray, List.length_flatten,
    Nat.sum_pos_iff_exists_pos, List.mem_map] at h
  obtain ⟨_, ⟨xs, m, rfl⟩, h⟩ := h
  exact ⟨xs, m, by simpa using h⟩

theorem getElem_zero_flatten {L : Array (Array α)} (h) :
    (flatten L)[0] = (L.findSome? fun l => l[0]?).get (getElem_zero_flatten.proof h) := by
  have t := getElem?_zero_flatten L
  simp [getElem?_eq_getElem, h] at t
  simp [← t]

theorem back?_flatten {L : Array (Array α)} :
    (flatten L).back? = (L.findSomeRev? fun l => l.back?) := by
  cases L using array_array_induction
  simp [List.getLast?_flatten, ← List.map_reverse, List.findSome?_map, Function.comp_def]

theorem findSome?_mkArray : findSome? f (mkArray n a) = if n = 0 then none else f a := by
  simp [mkArray_eq_toArray_replicate, List.findSome?_replicate]

@[simp] theorem findSome?_mkArray_of_pos (h : 0 < n) : findSome? f (mkArray n a) = f a := by
  simp [findSome?_mkArray, Nat.ne_of_gt h]

-- Argument is unused, but used to decide whether `simp` should unfold.
@[simp] theorem findSome?_mkArray_of_isSome (_ : (f a).isSome) :
   findSome? f (mkArray n a) = if n = 0 then none else f a := by
  simp [findSome?_mkArray]

@[simp] theorem findSome?_mkArray_of_isNone (h : (f a).isNone) :
    findSome? f (mkArray n a) = none := by
  rw [Option.isNone_iff_eq_none] at h
  simp [findSome?_mkArray, h]

/-! ### find? -/

@[simp] theorem find?_singleton (a : α) (p : α → Bool) :
    #[a].find? p = if p a then some a else none := by
  simp [singleton_eq_toArray_singleton]

@[simp] theorem findRev?_push_of_pos (l : Array α) (h : p a) :
    findRev? p (l.push a) = some a := by
  cases l; simp [h]

@[simp] theorem findRev?_cons_of_neg (l : Array α) (h : ¬p a) :
    findRev? p (l.push a) = findRev? p l := by
  cases l; simp [h]

@[simp] theorem find?_eq_none : find? p l = none ↔ ∀ x ∈ l, ¬ p x := by
  cases l; simp

theorem find?_eq_some_iff_append {xs : Array α} :
    xs.find? p = some b ↔ p b ∧ ∃ (as bs : Array α), xs = as.push b ++ bs ∧ ∀ a ∈ as, !p a := by
  rcases xs with ⟨xs⟩
  simp only [List.find?_toArray, List.find?_eq_some_iff_append, Bool.not_eq_eq_eq_not,
    Bool.not_true, exists_and_right, and_congr_right_iff]
  intro w
  constructor
  · rintro ⟨as, ⟨⟨x, rfl⟩, h⟩⟩
    exact ⟨as.toArray, ⟨x.toArray, by simp⟩ , by simpa using h⟩
  · rintro ⟨as, ⟨⟨x, h'⟩, h⟩⟩
    exact ⟨as.toList, ⟨x.toList, by simpa using congrArg Array.toList h'⟩,
      by simpa using h⟩

@[simp]
theorem find?_push_eq_some {xs : Array α} :
    (xs.push a).find? p = some b ↔ xs.find? p = some b ∨ (xs.find? p = none ∧ (p a ∧ a = b)) := by
  cases xs; simp

@[simp] theorem find?_isSome {xs : Array α} {p : α → Bool} : (xs.find? p).isSome ↔ ∃ x, x ∈ xs ∧ p x := by
  cases xs; simp

theorem find?_some {xs : Array α} (h : find? p xs = some a) : p a := by
  cases xs
  simp at h
  exact List.find?_some h

theorem mem_of_find?_eq_some {xs : Array α} (h : find? p xs = some a) : a ∈ xs := by
  cases xs
  simp at h
  simpa using List.mem_of_find?_eq_some h

theorem get_find?_mem {xs : Array α} (h) : (xs.find? p).get h ∈ xs := by
  cases xs
  simp [List.get_find?_mem]

@[simp] theorem find?_filter {xs : Array α} (p q : α → Bool) :
    (xs.filter p).find? q = xs.find? (fun a => p a ∧ q a) := by
  cases xs; simp

@[simp] theorem getElem?_zero_filter (p : α → Bool) (l : Array α) :
    (l.filter p)[0]? = l.find? p := by
  cases l; simp [← List.head?_eq_getElem?]

@[simp] theorem getElem_zero_filter (p : α → Bool) (l : Array α) (h) :
    (l.filter p)[0] =
      (l.find? p).get (by cases l; simpa [← List.countP_eq_length_filter] using h) := by
  cases l
  simp [List.getElem_zero_eq_head]

@[simp] theorem back?_filter (p : α → Bool) (l : Array α) : (l.filter p).back? = l.findRev? p := by
  cases l; simp

@[simp] theorem back!_filter [Inhabited α] (p : α → Bool) (l : Array α) :
    (l.filter p).back! = (l.findRev? p).get! := by
  cases l; simp [Option.get!_eq_getD]

@[simp] theorem find?_filterMap (xs : Array α) (f : α → Option β) (p : β → Bool) :
    (xs.filterMap f).find? p = (xs.find? (fun a => (f a).any p)).bind f := by
  cases xs; simp

@[simp] theorem find?_map (f : β → α) (xs : Array β) :
    find? p (xs.map f) = (xs.find? (p ∘ f)).map f := by
  cases xs; simp

@[simp] theorem find?_append {l₁ l₂ : Array α} :
    (l₁ ++ l₂).find? p = (l₁.find? p).or (l₂.find? p) := by
  cases l₁
  cases l₂
  simp

@[simp] theorem find?_flatten (xs : Array (Array α)) (p : α → Bool) :
    xs.flatten.find? p = xs.findSome? (·.find? p) := by
  cases xs using array_array_induction
  simp [List.findSome?_map, Function.comp_def]

theorem find?_flatten_eq_none {xs : Array (Array α)} {p : α → Bool} :
    xs.flatten.find? p = none ↔ ∀ ys ∈ xs, ∀ x ∈ ys, !p x := by
  simp

/--
If `find? p` returns `some a` from `xs.flatten`, then `p a` holds, and
some array in `xs` contains `a`, and no earlier element of that array satisfies `p`.
Moreover, no earlier array in `xs` has an element satisfying `p`.
-/
theorem find?_flatten_eq_some {xs : Array (Array α)} {p : α → Bool} {a : α} :
    xs.flatten.find? p = some a ↔
      p a ∧ ∃ (as : Array (Array α)) (ys zs : Array α) (bs : Array (Array α)),
        xs = as.push (ys.push a ++ zs) ++ bs ∧
        (∀ a ∈ as, ∀ x ∈ a, !p x) ∧ (∀ x ∈ ys, !p x) := by
  cases xs using array_array_induction
  simp only [flatten_toArray_map_toArray, List.find?_toArray, List.find?_flatten_eq_some]
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, exists_and_right, and_congr_right_iff]
  intro w
  constructor
  · rintro ⟨as, ys, ⟨⟨zs, bs, rfl⟩, h₁, h₂⟩⟩
    exact ⟨as.toArray.map List.toArray, ys.toArray,
      ⟨zs.toArray, bs.toArray.map List.toArray, by simp⟩, by simpa using h₁, by simpa using h₂⟩
  · rintro ⟨as, ys, ⟨⟨zs, bs, h⟩, h₁, h₂⟩⟩
    replace h := congrArg (·.map Array.toList) (congrArg Array.toList h)
    simp [Function.comp_def] at h
    exact ⟨as.toList.map Array.toList, ys.toList,
      ⟨zs.toList, bs.toList.map Array.toList, by simpa using h⟩,
        by simpa using h₁, by simpa using h₂⟩

@[simp] theorem find?_flatMap (xs : Array α) (f : α → Array β) (p : β → Bool) :
    (xs.flatMap f).find? p = xs.findSome? (fun x => (f x).find? p) := by
  cases xs
  simp [List.find?_flatMap, Array.flatMap_toArray]

theorem find?_flatMap_eq_none {xs : Array α} {f : α → Array β} {p : β → Bool} :
    (xs.flatMap f).find? p = none ↔ ∀ x ∈ xs, ∀ y ∈ f x, !p y := by
  simp

theorem find?_mkArray :
    find? p (mkArray n a) = if n = 0 then none else if p a then some a else none := by
  simp [mkArray_eq_toArray_replicate, List.find?_replicate]

@[simp] theorem find?_mkArray_of_length_pos (h : 0 < n) :
    find? p (mkArray n a) = if p a then some a else none := by
  simp [find?_mkArray, Nat.ne_of_gt h]

@[simp] theorem find?_mkArray_of_pos (h : p a) :
    find? p (mkArray n a) = if n = 0 then none else some a := by
  simp [find?_mkArray, h]

@[simp] theorem find?_mkArray_of_neg (h : ¬ p a) : find? p (mkArray n a) = none := by
  simp [find?_mkArray, h]

-- This isn't a `@[simp]` lemma since there is already a lemma for `l.find? p = none` for any `l`.
theorem find?_mkArray_eq_none {n : Nat} {a : α} {p : α → Bool} :
    (mkArray n a).find? p = none ↔ n = 0 ∨ !p a := by
  simp [mkArray_eq_toArray_replicate, List.find?_replicate_eq_none, Classical.or_iff_not_imp_left]

@[simp] theorem find?_mkArray_eq_some {n : Nat} {a b : α} {p : α → Bool} :
    (mkArray n a).find? p = some b ↔ n ≠ 0 ∧ p a ∧ a = b := by
  simp [mkArray_eq_toArray_replicate]

@[simp] theorem get_find?_mkArray (n : Nat) (a : α) (p : α → Bool) (h) :
    ((mkArray n a).find? p).get h = a := by
  simp [mkArray_eq_toArray_replicate]

theorem find?_pmap {P : α → Prop} (f : (a : α) → P a → β) (xs : Array α)
    (H : ∀ (a : α), a ∈ xs → P a) (p : β → Bool) :
    (xs.pmap f H).find? p = (xs.attach.find? (fun ⟨a, m⟩ => p (f a (H a m)))).map fun ⟨a, m⟩ => f a (H a m) := by
  simp only [pmap_eq_map_attach, find?_map]
  rfl

end Array
