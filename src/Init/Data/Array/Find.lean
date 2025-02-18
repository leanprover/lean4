/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.List.Nat.Find
import Init.Data.Array.Lemmas
import Init.Data.Array.Attach
import Init.Data.Array.Range

/-!
# Lemmas about `Array.findSome?`, `Array.find?, `Array.findIdx`, `Array.findIdx?`, `Array.idxOf`.
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

theorem find?_eq_findSome?_guard (l : Array α) : find? p l = findSome? (Option.guard fun x => p x) l :=
  (findSome?_guard l).symm

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
  cases L using array₂_induction
  simp [← List.head?_eq_getElem?, List.head?_flatten, List.findSome?_map, Function.comp_def]

theorem getElem_zero_flatten.proof {L : Array (Array α)} (h : 0 < L.flatten.size) :
    (L.findSome? fun l => l[0]?).isSome := by
  cases L using array₂_induction
  simp only [List.findSome?_toArray, List.findSome?_map, Function.comp_def, List.getElem?_toArray,
    List.findSome?_isSome_iff, isSome_getElem?]
  simp only [flatten_toArray_map_toArray, List.size_toArray, List.length_flatten,
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
  cases L using array₂_induction
  simp [List.getLast?_flatten, ← List.map_reverse, List.findSome?_map, Function.comp_def]

theorem findSome?_mkArray : findSome? f (mkArray n a) = if n = 0 then none else f a := by
  simp [← List.toArray_replicate, List.findSome?_replicate]

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
  cases xs using array₂_induction
  simp [List.findSome?_map, Function.comp_def]

theorem find?_flatten_eq_none_iff {xs : Array (Array α)} {p : α → Bool} :
    xs.flatten.find? p = none ↔ ∀ ys ∈ xs, ∀ x ∈ ys, !p x := by
  simp

@[deprecated find?_flatten_eq_none_iff (since := "2025-02-03")]
abbrev find?_flatten_eq_none := @find?_flatten_eq_none_iff

/--
If `find? p` returns `some a` from `xs.flatten`, then `p a` holds, and
some array in `xs` contains `a`, and no earlier element of that array satisfies `p`.
Moreover, no earlier array in `xs` has an element satisfying `p`.
-/
theorem find?_flatten_eq_some_iff {xs : Array (Array α)} {p : α → Bool} {a : α} :
    xs.flatten.find? p = some a ↔
      p a ∧ ∃ (as : Array (Array α)) (ys zs : Array α) (bs : Array (Array α)),
        xs = as.push (ys.push a ++ zs) ++ bs ∧
        (∀ a ∈ as, ∀ x ∈ a, !p x) ∧ (∀ x ∈ ys, !p x) := by
  cases xs using array₂_induction
  simp only [flatten_toArray_map_toArray, List.find?_toArray, List.find?_flatten_eq_some_iff]
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

@[deprecated find?_flatten_eq_some_iff (since := "2025-02-03")]
abbrev find?_flatten_eq_some := @find?_flatten_eq_some_iff

@[simp] theorem find?_flatMap (xs : Array α) (f : α → Array β) (p : β → Bool) :
    (xs.flatMap f).find? p = xs.findSome? (fun x => (f x).find? p) := by
  cases xs
  simp [List.find?_flatMap, Array.flatMap_toArray]

theorem find?_flatMap_eq_none_iff {xs : Array α} {f : α → Array β} {p : β → Bool} :
    (xs.flatMap f).find? p = none ↔ ∀ x ∈ xs, ∀ y ∈ f x, !p y := by
  simp

@[deprecated find?_flatMap_eq_none_iff (since := "2025-02-03")]
abbrev find?_flatMap_eq_none := @find?_flatMap_eq_none_iff

theorem find?_mkArray :
    find? p (mkArray n a) = if n = 0 then none else if p a then some a else none := by
  simp [← List.toArray_replicate, List.find?_replicate]

@[simp] theorem find?_mkArray_of_length_pos (h : 0 < n) :
    find? p (mkArray n a) = if p a then some a else none := by
  simp [find?_mkArray, Nat.ne_of_gt h]

@[simp] theorem find?_mkArray_of_pos (h : p a) :
    find? p (mkArray n a) = if n = 0 then none else some a := by
  simp [find?_mkArray, h]

@[simp] theorem find?_mkArray_of_neg (h : ¬ p a) : find? p (mkArray n a) = none := by
  simp [find?_mkArray, h]

-- This isn't a `@[simp]` lemma since there is already a lemma for `l.find? p = none` for any `l`.
theorem find?_mkArray_eq_none_iff {n : Nat} {a : α} {p : α → Bool} :
    (mkArray n a).find? p = none ↔ n = 0 ∨ !p a := by
  simp [← List.toArray_replicate, List.find?_replicate_eq_none_iff, Classical.or_iff_not_imp_left]

@[deprecated find?_mkArray_eq_none_iff (since := "2025-02-03")]
abbrev find?_mkArray_eq_none := @find?_mkArray_eq_none_iff

@[simp] theorem find?_mkArray_eq_some_iff {n : Nat} {a b : α} {p : α → Bool} :
    (mkArray n a).find? p = some b ↔ n ≠ 0 ∧ p a ∧ a = b := by
  simp [← List.toArray_replicate]

@[deprecated find?_mkArray_eq_some_iff (since := "2025-02-03")]
abbrev find?_mkArray_eq_some := @find?_mkArray_eq_some_iff

@[simp] theorem get_find?_mkArray (n : Nat) (a : α) (p : α → Bool) (h) :
    ((mkArray n a).find? p).get h = a := by
  simp [← List.toArray_replicate]

theorem find?_pmap {P : α → Prop} (f : (a : α) → P a → β) (xs : Array α)
    (H : ∀ (a : α), a ∈ xs → P a) (p : β → Bool) :
    (xs.pmap f H).find? p = (xs.attach.find? (fun ⟨a, m⟩ => p (f a (H a m)))).map fun ⟨a, m⟩ => f a (H a m) := by
  simp only [pmap_eq_map_attach, find?_map]
  rfl

theorem find?_eq_some_iff_getElem {xs : Array α} {p : α → Bool} {b : α} :
    xs.find? p = some b ↔ p b ∧ ∃ i h, xs[i] = b ∧ ∀ j : Nat, (hj : j < i) → !p xs[j] := by
  rcases xs with ⟨xs⟩
  simp [List.find?_eq_some_iff_getElem]

/-! ### findFinIdx? -/

@[simp] theorem findFinIdx?_empty {p : α → Bool} : findFinIdx? p #[] = none := rfl

-- We can't mark this as a `@[congr]` lemma since the head of the RHS is not `findFinIdx?`.
theorem findFinIdx?_congr {p : α → Bool} {l₁ : Array α} {l₂ : Array α} (w : l₁ = l₂) :
    findFinIdx? p l₁ = (findFinIdx? p l₂).map (fun i => i.cast (by simp [w])) := by
  subst w
  simp

@[simp] theorem findFinIdx?_subtype {p : α → Prop} {l : Array { x // p x }}
    {f : { x // p x } → Bool} {g : α → Bool} (hf : ∀ x h, f ⟨x, h⟩ = g x) :
    l.findFinIdx? f = (l.unattach.findFinIdx? g).map (fun i => i.cast (by simp)) := by
  cases l
  simp only [List.findFinIdx?_toArray, hf, List.findFinIdx?_subtype]
  rw [findFinIdx?_congr List.unattach_toArray]
  simp [Function.comp_def]

/-! ### findIdx -/

theorem findIdx_of_getElem?_eq_some {xs : Array α} (w : xs[xs.findIdx p]? = some y) : p y := by
  rcases xs with ⟨xs⟩
  exact List.findIdx_of_getElem?_eq_some (by simpa using w)

theorem findIdx_getElem {xs : Array α} {w : xs.findIdx p < xs.size} :
    p xs[xs.findIdx p] :=
  xs.findIdx_of_getElem?_eq_some (getElem?_eq_getElem w)

theorem findIdx_lt_size_of_exists {xs : Array α} (h : ∃ x ∈ xs, p x) :
    xs.findIdx p < xs.size := by
  rcases xs with ⟨xs⟩
  simpa using List.findIdx_lt_length_of_exists (by simpa using h)

theorem findIdx_getElem?_eq_getElem_of_exists {xs : Array α} (h : ∃ x ∈ xs, p x) :
    xs[xs.findIdx p]? = some (xs[xs.findIdx p]'(xs.findIdx_lt_size_of_exists h)) :=
  getElem?_eq_getElem (findIdx_lt_size_of_exists h)

@[simp]
theorem findIdx_eq_size {p : α → Bool} {xs : Array α} :
    xs.findIdx p = xs.size ↔ ∀ x ∈ xs, p x = false := by
  rcases xs with ⟨xs⟩
  simp

theorem findIdx_eq_size_of_false {p : α → Bool} {xs : Array α} (h : ∀ x ∈ xs, p x = false) :
    xs.findIdx p = xs.size := by
  rcases xs with ⟨xs⟩
  simp_all

theorem findIdx_le_size (p : α → Bool) {xs : Array α} : xs.findIdx p ≤ xs.size := by
  by_cases e : ∃ x ∈ xs, p x
  · exact Nat.le_of_lt (findIdx_lt_size_of_exists e)
  · simp at e
    exact Nat.le_of_eq (findIdx_eq_size.mpr e)

@[simp]
theorem findIdx_lt_size {p : α → Bool} {xs : Array α} :
    xs.findIdx p < xs.size ↔ ∃ x ∈ xs, p x := by
  rcases xs with ⟨xs⟩
  simp

/-- `p` does not hold for elements with indices less than `xs.findIdx p`. -/
theorem not_of_lt_findIdx {p : α → Bool} {xs : Array α} {i : Nat} (h : i < xs.findIdx p) :
    p (xs[i]'(Nat.le_trans h (findIdx_le_size p))) = false := by
  rcases xs with ⟨xs⟩
  simpa using List.not_of_lt_findIdx (by simpa using h)

/-- If `¬ p xs[j]` for all `j < i`, then `i ≤ xs.findIdx p`. -/
theorem le_findIdx_of_not {p : α → Bool} {xs : Array α} {i : Nat} (h : i < xs.size)
    (h2 : ∀ j (hji : j < i), p (xs[j]'(Nat.lt_trans hji h)) = false) : i ≤ xs.findIdx p := by
  apply Decidable.byContradiction
  intro f
  simp only [Nat.not_le] at f
  exact absurd (@findIdx_getElem _ p xs (Nat.lt_trans f h)) (by simpa using h2 (xs.findIdx p) f)

/-- If `¬ p xs[j]` for all `j ≤ i`, then `i < xs.findIdx p`. -/
theorem lt_findIdx_of_not {p : α → Bool} {xs : Array α} {i : Nat} (h : i < xs.size)
    (h2 : ∀ j (hji : j ≤ i), ¬p (xs[j]'(Nat.lt_of_le_of_lt hji h))) : i < xs.findIdx p := by
  apply Decidable.byContradiction
  intro f
  simp only [Nat.not_lt] at f
  exact absurd (@findIdx_getElem _ p xs (Nat.lt_of_le_of_lt f h)) (h2 (xs.findIdx p) f)

/-- `xs.findIdx p = i` iff `p xs[i]` and `¬ p xs [j]` for all `j < i`. -/
theorem findIdx_eq {p : α → Bool} {xs : Array α} {i : Nat} (h : i < xs.size) :
    xs.findIdx p = i ↔ p xs[i] ∧ ∀ j (hji : j < i), p (xs[j]'(Nat.lt_trans hji h)) = false := by
  refine ⟨fun f ↦ ⟨f ▸ (@findIdx_getElem _ p xs (f ▸ h)), fun _ hji ↦ not_of_lt_findIdx (f ▸ hji)⟩,
    fun ⟨_, h2⟩ ↦ ?_⟩
  apply Nat.le_antisymm _ (le_findIdx_of_not h h2)
  apply Decidable.byContradiction
  intro h3
  simp at h3
  simp_all [not_of_lt_findIdx h3]

theorem findIdx_append (p : α → Bool) (l₁ l₂ : Array α) :
    (l₁ ++ l₂).findIdx p =
      if l₁.findIdx p < l₁.size then l₁.findIdx p else l₂.findIdx p + l₁.size := by
  rcases l₁ with ⟨l₁⟩
  rcases l₂ with ⟨l₂⟩
  simp [List.findIdx_append]

theorem findIdx_le_findIdx {l : Array α} {p q : α → Bool} (h : ∀ x ∈ l, p x → q x) : l.findIdx q ≤ l.findIdx p := by
  rcases l with ⟨l⟩
  simp_all [List.findIdx_le_findIdx]

@[simp] theorem findIdx_subtype {p : α → Prop} {l : Array { x // p x }}
    {f : { x // p x } → Bool} {g : α → Bool} (hf : ∀ x h, f ⟨x, h⟩ = g x) :
    l.findIdx f = l.unattach.findIdx g := by
  cases l
  simp [hf]

theorem false_of_mem_extract_findIdx {xs : Array α} {p : α → Bool} (h : x ∈ xs.extract 0 (xs.findIdx p)) :
    p x = false := by
  rcases xs with ⟨xs⟩
  exact List.false_of_mem_take_findIdx (by simpa using h)

@[simp] theorem findIdx_extract {xs : Array α} {i : Nat} {p : α → Bool} :
    (xs.extract 0 i).findIdx p = min i (xs.findIdx p) := by
  cases xs
  simp

@[simp] theorem min_findIdx_findIdx {xs : Array α} {p q : α → Bool} :
    min (xs.findIdx p) (xs.findIdx q) = xs.findIdx (fun a => p a || q a) := by
  cases xs
  simp

/-! ### findIdx? -/

@[simp] theorem findIdx?_empty : (#[] : Array α).findIdx? p = none := rfl

@[simp]
theorem findIdx?_eq_none_iff {xs : Array α} {p : α → Bool} :
    xs.findIdx? p = none ↔ ∀ x, x ∈ xs → p x = false := by
  rcases xs with ⟨xs⟩
  simp

theorem findIdx?_isSome {xs : Array α} {p : α → Bool} :
    (xs.findIdx? p).isSome = xs.any p := by
  rcases xs with ⟨xs⟩
  simp [List.findIdx?_isSome]

theorem findIdx?_isNone {xs : Array α} {p : α → Bool} :
    (xs.findIdx? p).isNone = xs.all (¬p ·) := by
  rcases xs with ⟨xs⟩
  simp [List.findIdx?_isNone]

theorem findIdx?_eq_some_iff_findIdx_eq {xs : Array α} {p : α → Bool} {i : Nat} :
    xs.findIdx? p = some i ↔ i < xs.size ∧ xs.findIdx p = i := by
  rcases xs with ⟨xs⟩
  simp [List.findIdx?_eq_some_iff_findIdx_eq]

theorem findIdx?_eq_some_of_exists {xs : Array α} {p : α → Bool} (h : ∃ x, x ∈ xs ∧ p x) :
    xs.findIdx? p = some (xs.findIdx p) := by
  rw [findIdx?_eq_some_iff_findIdx_eq]
  exact ⟨findIdx_lt_size_of_exists h, rfl⟩

theorem findIdx?_eq_none_iff_findIdx_eq {xs : Array α} {p : α → Bool} :
    xs.findIdx? p = none ↔ xs.findIdx p = xs.size := by
  rcases xs with ⟨xs⟩
  simp [List.findIdx?_eq_none_iff_findIdx_eq]

theorem findIdx?_eq_guard_findIdx_lt {xs : Array α} {p : α → Bool} :
    xs.findIdx? p = Option.guard (fun i => i < xs.size) (xs.findIdx p) := by
  rcases xs with ⟨xs⟩
  simp [List.findIdx?_eq_guard_findIdx_lt]

theorem findIdx?_eq_some_iff_getElem {xs : Array α} {p : α → Bool} {i : Nat} :
    xs.findIdx? p = some i ↔
      ∃ h : i < xs.size, p xs[i] ∧ ∀ j (hji : j < i), ¬p (xs[j]'(Nat.lt_trans hji h)) := by
  rcases xs with ⟨xs⟩
  simp [List.findIdx?_eq_some_iff_getElem]

theorem of_findIdx?_eq_some {xs : Array α} {p : α → Bool} (w : xs.findIdx? p = some i) :
    match xs[i]? with | some a => p a | none => false := by
  rcases xs with ⟨xs⟩
  simpa using List.of_findIdx?_eq_some (by simpa using w)

theorem of_findIdx?_eq_none {xs : Array α} {p : α → Bool} (w : xs.findIdx? p = none) :
    ∀ i : Nat, match xs[i]? with | some a => ¬ p a | none => true := by
  rcases xs with ⟨xs⟩
  simpa using List.of_findIdx?_eq_none (by simpa using w)

@[simp] theorem findIdx?_map (f : β → α) (l : Array β) : findIdx? p (l.map f) = l.findIdx? (p ∘ f) := by
  rcases l with ⟨l⟩
  simp [List.findIdx?_map]

@[simp] theorem findIdx?_append :
    (xs ++ ys : Array α).findIdx? p =
      (xs.findIdx? p).or ((ys.findIdx? p).map fun i => i + xs.size) := by
  rcases xs with ⟨xs⟩
  rcases ys with ⟨ys⟩
  simp [List.findIdx?_append]

theorem findIdx?_flatten {l : Array (Array α)} {p : α → Bool} :
    l.flatten.findIdx? p =
      (l.findIdx? (·.any p)).map
        fun i => ((l.take i).map Array.size).sum +
          (l[i]?.map fun xs => xs.findIdx p).getD 0 := by
  cases l using array₂_induction
  simp [List.findIdx?_flatten, Function.comp_def]

@[simp] theorem findIdx?_mkArray :
    (mkArray n a).findIdx? p = if 0 < n ∧ p a then some 0 else none := by
  rw [← List.toArray_replicate]
  simp only [List.findIdx?_toArray]
  simp

theorem findIdx?_eq_findSome?_zipIdx {xs : Array α} {p : α → Bool} :
    xs.findIdx? p = xs.zipIdx.findSome? fun ⟨a, i⟩ => if p a then some i else none := by
  rcases xs with ⟨xs⟩
  simp [List.findIdx?_eq_findSome?_zipIdx]

theorem findIdx?_eq_fst_find?_zipIdx {xs : Array α} {p : α → Bool} :
    xs.findIdx? p = (xs.zipIdx.find? fun ⟨x, _⟩ => p x).map (·.2) := by
  rcases xs with ⟨xs⟩
  simp [List.findIdx?_eq_fst_find?_zipIdx]

-- See also `findIdx_le_findIdx`.
theorem findIdx?_eq_none_of_findIdx?_eq_none {xs : Array α} {p q : α → Bool} (w : ∀ x ∈ xs, p x → q x) :
    xs.findIdx? q = none → xs.findIdx? p = none := by
  rcases xs with ⟨xs⟩
  simpa using List.findIdx?_eq_none_of_findIdx?_eq_none (by simpa using w)

theorem findIdx_eq_getD_findIdx? {xs : Array α} {p : α → Bool} :
    xs.findIdx p = (xs.findIdx? p).getD xs.size := by
  rcases xs with ⟨xs⟩
  simp [List.findIdx_eq_getD_findIdx?]

theorem findIdx?_eq_some_le_of_findIdx?_eq_some {xs : Array α} {p q : α → Bool} (w : ∀ x ∈ xs, p x → q x) {i : Nat}
    (h : xs.findIdx? p = some i) : ∃ j, j ≤ i ∧ xs.findIdx? q = some j := by
  rcases xs with ⟨xs⟩
  simp [List.findIdx?_eq_some_le_of_findIdx?_eq_some (by simpa using w) (by simpa using h)]

@[simp] theorem findIdx?_subtype {p : α → Prop} {l : Array { x // p x }}
    {f : { x // p x } → Bool} {g : α → Bool} (hf : ∀ x h, f ⟨x, h⟩ = g x) :
    l.findIdx? f = l.unattach.findIdx? g := by
  cases l
  simp [hf]

@[simp] theorem findIdx?_take {xs : Array α} {i : Nat} {p : α → Bool} :
    (xs.take i).findIdx? p = (xs.findIdx? p).bind (Option.guard (fun j => j < i)) := by
  cases xs
  simp

/-! ### idxOf

The verification API for `idxOf` is still incomplete.
The lemmas below should be made consistent with those for `findIdx` (and proved using them).
-/

theorem idxOf_append [BEq α] [LawfulBEq α] {l₁ l₂ : Array α} {a : α} :
    (l₁ ++ l₂).idxOf a = if a ∈ l₁ then l₁.idxOf a else l₂.idxOf a + l₁.size := by
  rw [idxOf, findIdx_append]
  split <;> rename_i h
  · rw [if_pos]
    simpa using h
  · rw [if_neg]
    simpa using h

theorem idxOf_eq_size [BEq α] [LawfulBEq α] {l : Array α} (h : a ∉ l) : l.idxOf a = l.size := by
  rcases l with ⟨l⟩
  simp [List.idxOf_eq_length (by simpa using h)]

theorem idxOf_lt_length [BEq α] [LawfulBEq α] {l : Array α} (h : a ∈ l) : l.idxOf a < l.size := by
  rcases l with ⟨l⟩
  simp [List.idxOf_lt_length (by simpa using h)]


/-! ### idxOf?

The verification API for `idxOf?` is still incomplete.
The lemmas below should be made consistent with those for `findIdx?` (and proved using them).
-/

@[simp] theorem idxOf?_empty [BEq α] : (#[] : Array α).idxOf? a = none := rfl

@[simp] theorem idxOf?_eq_none_iff [BEq α] [LawfulBEq α] {l : Array α} {a : α} :
    l.idxOf? a = none ↔ a ∉ l := by
  rcases l with ⟨l⟩
  simp [List.idxOf?_eq_none_iff]

/-! ### finIdxOf? -/

theorem idxOf?_eq_map_finIdxOf?_val [BEq α] {xs : Array α} {a : α} :
    xs.idxOf? a = (xs.finIdxOf? a).map (·.val) := by
  simp [idxOf?, finIdxOf?, findIdx?_eq_map_findFinIdx?_val]

end Array
