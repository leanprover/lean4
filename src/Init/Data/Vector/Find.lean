/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.Vector.Lemmas
import Init.Data.Vector.Attach
import Init.Data.Vector.Range
import Init.Data.Array.Find

/-!
# Lemmas about `Vector.findSome?`, `Vector.find?`, `Vector.findFinIdx?`.

We are still missing results about `idxOf?`, `findIdx`, and `findIdx?`.
-/

namespace Vector

open Nat

/-! ### findSome? -/

@[simp] theorem findSomeRev?_push_of_isSome (l : Vector α n) (h : (f a).isSome) : (l.push a).findSomeRev? f = f a := by
  rcases l with ⟨l, rfl⟩
  simp only [push_mk, findSomeRev?_mk, Array.findSomeRev?_push_of_isSome, h]

@[simp] theorem findSomeRev?_push_of_isNone (l : Vector α n) (h : (f a).isNone) : (l.push a).findSomeRev? f = l.findSomeRev? f := by
  rcases l with ⟨l, rfl⟩
  simp only [push_mk, findSomeRev?_mk, Array.findSomeRev?_push_of_isNone, h]

theorem exists_of_findSome?_eq_some {f : α → Option β} {l : Vector α n} (w : l.findSome? f = some b) :
    ∃ a, a ∈ l ∧ f a = b := by
  rcases l with ⟨l, rfl⟩
  simpa using Array.exists_of_findSome?_eq_some (by simpa using w)

@[simp] theorem findSome?_eq_none_iff {f : α → Option β} {l : Vector α n} :
    findSome? f l = none ↔ ∀ x ∈ l, f x = none := by
  cases l; simp

@[simp] theorem findSome?_isSome_iff {f : α → Option β} {l : Vector α n} :
    (l.findSome? f).isSome ↔ ∃ x, x ∈ l ∧ (f x).isSome := by
  cases l; simp

theorem findSome?_eq_some_iff {f : α → Option β} {l : Vector α n} {b : β} :
    l.findSome? f = some b ↔
      ∃ (k₁ k₂ : Nat) (w : n = k₁ + 1 + k₂) (l₁ : Vector α k₁) (a : α) (l₂ : Vector α k₂),
        l = (l₁.push a ++ l₂).cast w.symm ∧ f a = some b ∧ ∀ x ∈ l₁, f x = none := by
  rcases l with ⟨l, rfl⟩
  simp only [findSome?_mk, mk_eq]
  rw [Array.findSome?_eq_some_iff]
  constructor
  · rintro ⟨l₁, a, l₂, rfl, h₁, h₂⟩
    exact ⟨l₁.size, l₂.size, by simp, ⟨l₁, rfl⟩, a, ⟨l₂, rfl⟩, by simp, h₁, by simpa using h₂⟩
  · rintro ⟨k₁, k₂, h, l₁, a, l₂, w, h₁, h₂⟩
    exact ⟨l₁.toArray, a, l₂.toArray, by simp [w], h₁, by simpa using h₂⟩

@[simp] theorem findSome?_guard (l : Vector α n) : findSome? (Option.guard fun x => p x) l = find? p l := by
  cases l; simp

theorem find?_eq_findSome?_guard (l : Vector α n) : find? p l = findSome? (Option.guard fun x => p x) l :=
  (findSome?_guard l).symm

@[simp] theorem map_findSome? (f : α → Option β) (g : β → γ) (l : Vector α n) :
    (l.findSome? f).map g = l.findSome? (Option.map g ∘ f) := by
  cases l; simp

theorem findSome?_map (f : β → γ) (l : Vector β n) : findSome? p (l.map f) = l.findSome? (p ∘ f) := by
  rcases l with ⟨l, rfl⟩
  simp [Array.findSome?_map]

theorem findSome?_append {l₁ : Vector α n₁} {l₂ : Vector α n₂} : (l₁ ++ l₂).findSome? f = (l₁.findSome? f).or (l₂.findSome? f) := by
  cases l₁; cases l₂; simp [Array.findSome?_append]

theorem getElem?_zero_flatten (L : Vector (Vector α m) n) :
    (flatten L)[0]? = L.findSome? fun l => l[0]? := by
  cases L using vector₂_induction
  simp [Array.getElem?_zero_flatten, Array.findSome?_map, Function.comp_def]

theorem getElem_zero_flatten.proof {L : Vector (Vector α m) n} (h : 0 < n * m) :
    (L.findSome? fun l => l[0]?).isSome := by
  cases L using vector₂_induction with
  | of xss h₁ h₂ =>
    have hn : 0 < n := Nat.pos_of_mul_pos_right h
    have hm : 0 < m := Nat.pos_of_mul_pos_left h
    simp only [hm, getElem?_eq_getElem, findSome?_mk, Array.findSome?_isSome_iff, Array.mem_map,
      Array.mem_attach, mk_eq, true_and, Subtype.exists, exists_prop, exists_eq_right,
      Option.isSome_some, and_true]
    exact ⟨⟨xss[0], h₂ _ (by simp)⟩, by simp⟩

theorem getElem_zero_flatten {L : Vector (Vector α m) n} (h : 0 < n * m) :
    (flatten L)[0] = (L.findSome? fun l => l[0]?).get (getElem_zero_flatten.proof h) := by
  have t := getElem?_zero_flatten L
  simp [getElem?_eq_getElem, h] at t
  simp [← t]

theorem findSome?_mkVector : findSome? f (mkVector n a) = if n = 0 then none else f a := by
  rw [mkVector_eq_mk_mkArray, findSome?_mk, Array.findSome?_mkArray]

@[simp] theorem findSome?_mkVector_of_pos (h : 0 < n) : findSome? f (mkVector n a) = f a := by
  simp [findSome?_mkVector, Nat.ne_of_gt h]

-- Argument is unused, but used to decide whether `simp` should unfold.
@[simp] theorem findSome?_mkVector_of_isSome (_ : (f a).isSome) :
   findSome? f (mkVector n a) = if n = 0 then none else f a := by
  simp [findSome?_mkVector]

@[simp] theorem findSome?_mkVector_of_isNone (h : (f a).isNone) :
    findSome? f (mkVector n a) = none := by
  rw [Option.isNone_iff_eq_none] at h
  simp [findSome?_mkVector, h]

/-! ### find? -/

@[simp] theorem find?_singleton (a : α) (p : α → Bool) :
    #v[a].find? p = if p a then some a else none := by
  simp

@[simp] theorem findRev?_push_of_pos (l : Vector α n) (h : p a) :
    findRev? p (l.push a) = some a := by
  cases l; simp [h]

@[simp] theorem findRev?_cons_of_neg (l : Vector α n) (h : ¬p a) :
    findRev? p (l.push a) = findRev? p l := by
  cases l; simp [h]

@[simp] theorem find?_eq_none : find? p l = none ↔ ∀ x ∈ l, ¬ p x := by
  cases l; simp

theorem find?_eq_some_iff_append {xs : Vector α n} :
    xs.find? p = some b ↔
      p b ∧ ∃ (k₁ k₂ : Nat) (w : n = k₁ + 1 + k₂) (as : Vector α k₁) (bs : Vector α k₂),
        xs = (as.push b ++ bs).cast w.symm ∧ ∀ a ∈ as, !p a := by
  rcases xs with ⟨xs, rfl⟩
  simp only [find?_mk, Array.find?_eq_some_iff_append,
    mk_eq, toArray_cast, toArray_append, toArray_push]
  constructor
  · rintro ⟨h, as, bs, rfl, w⟩
    exact ⟨h, as.size, bs.size, by simp, ⟨as, rfl⟩, ⟨bs, rfl⟩, by simp, by simpa using w⟩
  · rintro ⟨h, k₁, k₂, w, as, bs, h', w'⟩
    exact ⟨h, as.toArray, bs.toArray, by simp [h'], by simpa using w'⟩

@[simp]
theorem find?_push_eq_some {xs : Vector α n} :
    (xs.push a).find? p = some b ↔ xs.find? p = some b ∨ (xs.find? p = none ∧ (p a ∧ a = b)) := by
  cases xs; simp

@[simp] theorem find?_isSome {xs : Vector α n} {p : α → Bool} : (xs.find? p).isSome ↔ ∃ x, x ∈ xs ∧ p x := by
  cases xs; simp

theorem find?_some {xs : Vector α n} (h : find? p xs = some a) : p a := by
  rcases xs with ⟨xs, rfl⟩
  simp at h
  exact Array.find?_some h

theorem mem_of_find?_eq_some {xs : Vector α n} (h : find? p xs = some a) : a ∈ xs := by
  cases xs
  simp at h
  simpa using Array.mem_of_find?_eq_some h

theorem get_find?_mem {xs : Vector α n} (h) : (xs.find? p).get h ∈ xs := by
  cases xs
  simp [Array.get_find?_mem]

@[simp] theorem find?_filter {xs : Vector α n} (p q : α → Bool) :
    (xs.filter p).find? q = xs.find? (fun a => p a ∧ q a) := by
  cases xs; simp

@[simp] theorem getElem?_zero_filter (p : α → Bool) (l : Vector α n) :
    (l.filter p)[0]? = l.find? p := by
  cases l; simp [← List.head?_eq_getElem?]

@[simp] theorem getElem_zero_filter (p : α → Bool) (l : Vector α n) (h) :
    (l.filter p)[0] =
      (l.find? p).get (by cases l; simpa [← Array.countP_eq_size_filter] using h) := by
  cases l
  simp [List.getElem_zero_eq_head]

@[simp] theorem find?_map (f : β → α) (xs : Vector β n) :
    find? p (xs.map f) = (xs.find? (p ∘ f)).map f := by
  cases xs; simp

@[simp] theorem find?_append {l₁ : Vector α n₁} {l₂ : Vector α n₂} :
    (l₁ ++ l₂).find? p = (l₁.find? p).or (l₂.find? p) := by
  cases l₁
  cases l₂
  simp

@[simp] theorem find?_flatten (xs : Vector (Vector α m) n) (p : α → Bool) :
    xs.flatten.find? p = xs.findSome? (·.find? p) := by
  cases xs using vector₂_induction
  simp [Array.findSome?_map, Function.comp_def]

theorem find?_flatten_eq_none_iff {xs : Vector (Vector α m) n} {p : α → Bool} :
    xs.flatten.find? p = none ↔ ∀ ys ∈ xs, ∀ x ∈ ys, !p x := by
  simp

@[simp] theorem find?_flatMap (xs : Vector α n) (f : α → Vector β m) (p : β → Bool) :
    (xs.flatMap f).find? p = xs.findSome? (fun x => (f x).find? p) := by
  cases xs
  simp [Array.find?_flatMap, Array.flatMap_toArray]


theorem find?_flatMap_eq_none_iff {xs : Vector α n} {f : α → Vector β m} {p : β → Bool} :
    (xs.flatMap f).find? p = none ↔ ∀ x ∈ xs, ∀ y ∈ f x, !p y := by
  simp

theorem find?_mkVector :
    find? p (mkVector n a) = if n = 0 then none else if p a then some a else none := by
  rw [mkVector_eq_mk_mkArray, find?_mk, Array.find?_mkArray]

@[simp] theorem find?_mkVector_of_length_pos (h : 0 < n) :
    find? p (mkVector n a) = if p a then some a else none := by
  simp [find?_mkVector, Nat.ne_of_gt h]

@[simp] theorem find?_mkVector_of_pos (h : p a) :
    find? p (mkVector n a) = if n = 0 then none else some a := by
  simp [find?_mkVector, h]

@[simp] theorem find?_mkVector_of_neg (h : ¬ p a) : find? p (mkVector n a) = none := by
  simp [find?_mkVector, h]

-- This isn't a `@[simp]` lemma since there is already a lemma for `l.find? p = none` for any `l`.
theorem find?_mkVector_eq_none_iff {n : Nat} {a : α} {p : α → Bool} :
    (mkVector n a).find? p = none ↔ n = 0 ∨ !p a := by
  simp [Classical.or_iff_not_imp_left]

@[simp] theorem find?_mkVector_eq_some_iff {n : Nat} {a b : α} {p : α → Bool} :
    (mkVector n a).find? p = some b ↔ n ≠ 0 ∧ p a ∧ a = b := by
  rw [mkVector_eq_mk_mkArray, find?_mk]
  simp

@[simp] theorem get_find?_mkVector (n : Nat) (a : α) (p : α → Bool) (h) :
    ((mkVector n a).find? p).get h = a := by
  simp only [mkVector_eq_mk_mkArray, find?_mk]
  simp

theorem find?_pmap {P : α → Prop} (f : (a : α) → P a → β) (xs : Vector α n)
    (H : ∀ (a : α), a ∈ xs → P a) (p : β → Bool) :
    (xs.pmap f H).find? p = (xs.attach.find? (fun ⟨a, m⟩ => p (f a (H a m)))).map fun ⟨a, m⟩ => f a (H a m) := by
  simp only [pmap_eq_map_attach, find?_map]
  rfl

theorem find?_eq_some_iff_getElem {xs : Vector α n} {p : α → Bool} {b : α} :
    xs.find? p = some b ↔ p b ∧ ∃ i h, xs[i] = b ∧ ∀ j : Nat, (hj : j < i) → !p xs[j] := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.find?_eq_some_iff_getElem]

/-! ### findFinIdx? -/

@[simp] theorem findFinIdx?_empty {p : α → Bool} : findFinIdx? p (#v[] : Vector α 0) = none := rfl

@[congr] theorem findFinIdx?_congr {p : α → Bool} {l₁ : Vector α n} {l₂ : Vector α n} (w : l₁ = l₂) :
    findFinIdx? p l₁ = findFinIdx? p l₂ := by
  subst w
  simp

@[simp] theorem findFinIdx?_subtype {p : α → Prop} {l : Vector { x // p x } n}
    {f : { x // p x } → Bool} {g : α → Bool} (hf : ∀ x h, f ⟨x, h⟩ = g x) :
    l.findFinIdx? f = l.unattach.findFinIdx? g := by
  rcases l with ⟨l, rfl⟩
  simp [hf, Function.comp_def]

end Vector
