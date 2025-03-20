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

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace Vector

open Nat

/-! ### findSome? -/

@[simp] theorem findSomeRev?_push_of_isSome (xs : Vector α n) (h : (f a).isSome) : (xs.push a).findSomeRev? f = f a := by
  rcases xs with ⟨xs, rfl⟩
  simp only [push_mk, findSomeRev?_mk, Array.findSomeRev?_push_of_isSome, h]

@[simp] theorem findSomeRev?_push_of_isNone (xs : Vector α n) (h : (f a).isNone) : (xs.push a).findSomeRev? f = xs.findSomeRev? f := by
  rcases xs with ⟨xs, rfl⟩
  simp only [push_mk, findSomeRev?_mk, Array.findSomeRev?_push_of_isNone, h]

theorem exists_of_findSome?_eq_some {f : α → Option β} {xs : Vector α n} (w : xs.findSome? f = some b) :
    ∃ a, a ∈ xs ∧ f a = b := by
  rcases xs with ⟨xs, rfl⟩
  simpa using Array.exists_of_findSome?_eq_some (by simpa using w)

@[simp] theorem findSome?_eq_none_iff {f : α → Option β} {xs : Vector α n} :
    xs.findSome? f = none ↔ ∀ x ∈ xs, f x = none := by
  rcases xs with ⟨xs, rfl⟩
  simp

@[simp] theorem findSome?_isSome_iff {f : α → Option β} {xs : Vector α n} :
    (xs.findSome? f).isSome ↔ ∃ x, x ∈ xs ∧ (f x).isSome := by
  rcases xs with ⟨xs, rfl⟩
  simp

theorem findSome?_eq_some_iff {f : α → Option β} {xs : Vector α n} {b : β} :
    xs.findSome? f = some b ↔
      ∃ (k₁ k₂ : Nat) (w : n = k₁ + 1 + k₂) (ys : Vector α k₁) (a : α) (zs : Vector α k₂),
        xs = (ys.push a ++ zs).cast w.symm ∧ f a = some b ∧ ∀ x ∈ ys, f x = none := by
  rcases xs with ⟨xs, rfl⟩
  simp only [findSome?_mk, mk_eq]
  rw [Array.findSome?_eq_some_iff]
  constructor
  · rintro ⟨ys, a, zs, rfl, h₁, h₂⟩
    exact ⟨ys.size, zs.size, by simp, ⟨ys, rfl⟩, a, ⟨zs, rfl⟩, by simp, h₁, by simpa using h₂⟩
  · rintro ⟨k₁, k₂, h, ys, a, zs, w, h₁, h₂⟩
    exact ⟨ys.toArray, a, zs.toArray, by simp [w], h₁, by simpa using h₂⟩

@[simp] theorem findSome?_guard (xs : Vector α n) : findSome? (Option.guard fun x => p x) xs = find? p xs := by
  rcases xs with ⟨xs, rfl⟩
  simp

theorem find?_eq_findSome?_guard (xs : Vector α n) : find? p xs = findSome? (Option.guard fun x => p x) xs :=
  (findSome?_guard xs).symm

@[simp] theorem map_findSome? (f : α → Option β) (g : β → γ) (xs : Vector α n) :
    (xs.findSome? f).map g = xs.findSome? (Option.map g ∘ f) := by
  cases xs; simp

theorem findSome?_map (f : β → γ) (xs : Vector β n) : findSome? p (xs.map f) = xs.findSome? (p ∘ f) := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.findSome?_map]

theorem findSome?_append {xs : Vector α n₁} {ys : Vector α n₂} : (xs ++ ys).findSome? f = (xs.findSome? f).or (ys.findSome? f) := by
  cases xs; cases ys; simp [Array.findSome?_append]

theorem getElem?_zero_flatten (xss : Vector (Vector α m) n) :
    (flatten xss)[0]? = xss.findSome? fun xs => xs[0]? := by
  cases xss using vector₂_induction
  simp [Array.getElem?_zero_flatten, Array.findSome?_map, Function.comp_def]

theorem getElem_zero_flatten.proof {xss : Vector (Vector α m) n} (h : 0 < n * m) :
    (xss.findSome? fun xs => xs[0]?).isSome := by
  cases xss using vector₂_induction with
  | of xss h₁ h₂ =>
    have hn : 0 < n := Nat.pos_of_mul_pos_right h
    have hm : 0 < m := Nat.pos_of_mul_pos_left h
    simp only [hm, getElem?_eq_getElem, findSome?_mk, Array.findSome?_isSome_iff, Array.mem_map,
      Array.mem_attach, mk_eq, true_and, Subtype.exists, exists_prop, exists_eq_right,
      Option.isSome_some, and_true]
    exact ⟨⟨xss[0], h₂ _ (by simp)⟩, by simp⟩

theorem getElem_zero_flatten {xss : Vector (Vector α m) n} (h : 0 < n * m) :
    (flatten xss)[0] = (xss.findSome? fun xs => xs[0]?).get (getElem_zero_flatten.proof h) := by
  have t := getElem?_zero_flatten xss
  simp [getElem?_eq_getElem, h] at t
  simp [← t]

theorem findSome?_replicate : findSome? f (replicate n a) = if n = 0 then none else f a := by
  rw [replicate_eq_mk_replicate, findSome?_mk, Array.findSome?_replicate]

@[deprecated findSome?_replicate (since := "2025-03-18")]
abbrev findSome?_mkVector := @findSome?_replicate

@[simp] theorem findSome?_replicate_of_pos (h : 0 < n) : findSome? f (replicate n a) = f a := by
  simp [findSome?_replicate, Nat.ne_of_gt h]

@[deprecated findSome?_replicate_of_pos (since := "2025-03-18")]
abbrev findSome?_mkVector_of_pos := @findSome?_replicate_of_pos

-- Argument is unused, but used to decide whether `simp` should unfold.
@[simp] theorem findSome?_replicate_of_isSome (_ : (f a).isSome) :
   findSome? f (replicate n a) = if n = 0 then none else f a := by
  simp [findSome?_replicate]

@[deprecated findSome?_replicate_of_isSome (since := "2025-03-18")]
abbrev findSome?_mkVector_of_isSome := @findSome?_replicate_of_isSome

@[simp] theorem findSome?_replicate_of_isNone (h : (f a).isNone) :
    findSome? f (replicate n a) = none := by
  rw [Option.isNone_iff_eq_none] at h
  simp [findSome?_replicate, h]

@[deprecated findSome?_replicate_of_isNone (since := "2025-03-18")]
abbrev findSome?_mkVector_of_isNone := @findSome?_replicate_of_isNone

/-! ### find? -/

@[simp] theorem find?_singleton (a : α) (p : α → Bool) :
    #v[a].find? p = if p a then some a else none := by
  simp

@[simp] theorem findRev?_push_of_pos (xs : Vector α n) (h : p a) :
    findRev? p (xs.push a) = some a := by
  cases xs; simp [h]

@[simp] theorem findRev?_cons_of_neg (xs : Vector α n) (h : ¬p a) :
    findRev? p (xs.push a) = findRev? p xs := by
  cases xs; simp [h]

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

@[simp] theorem getElem?_zero_filter (p : α → Bool) (xs : Vector α n) :
    (xs.filter p)[0]? = xs.find? p := by
  cases xs; simp [← List.head?_eq_getElem?]

@[simp] theorem getElem_zero_filter (p : α → Bool) (xs : Vector α n) (h) :
    (xs.filter p)[0] =
      (xs.find? p).get (by cases xs; simpa [← Array.countP_eq_size_filter] using h) := by
  cases xs
  simp [List.getElem_zero_eq_head]

@[simp] theorem find?_map (f : β → α) (xs : Vector β n) :
    find? p (xs.map f) = (xs.find? (p ∘ f)).map f := by
  cases xs; simp

@[simp] theorem find?_append {xs : Vector α n₁} {ys : Vector α n₂} :
    (xs ++ ys).find? p = (xs.find? p).or (ys.find? p) := by
  cases xs
  cases ys
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

theorem find?_replicate :
    find? p (replicate n a) = if n = 0 then none else if p a then some a else none := by
  rw [replicate_eq_mk_replicate, find?_mk, Array.find?_replicate]

@[deprecated find?_replicate (since := "2025-03-18")]
abbrev find?_mkVector := @find?_replicate

@[simp] theorem find?_replicate_of_size_pos (h : 0 < n) :
    find? p (replicate n a) = if p a then some a else none := by
  simp [find?_replicate, Nat.ne_of_gt h]

@[deprecated find?_replicate_of_size_pos (since := "2025-03-18")]
abbrev find?_mkVector_of_length_pos := @find?_replicate_of_size_pos

@[simp] theorem find?_replicate_of_pos (h : p a) :
    find? p (replicate n a) = if n = 0 then none else some a := by
  simp [find?_replicate, h]

@[deprecated find?_replicate_of_pos (since := "2025-03-18")]
abbrev find?_mkVector_of_pos := @find?_replicate_of_pos

@[simp] theorem find?_replicate_of_neg (h : ¬ p a) : find? p (replicate n a) = none := by
  simp [find?_replicate, h]

@[deprecated find?_replicate_of_neg (since := "2025-03-18")]
abbrev find?_mkVector_of_neg := @find?_replicate_of_neg

-- This isn't a `@[simp]` lemma since there is already a lemma for `l.find? p = none` for any `l`.
theorem find?_replicate_eq_none_iff {n : Nat} {a : α} {p : α → Bool} :
    (replicate n a).find? p = none ↔ n = 0 ∨ !p a := by
  simp [Classical.or_iff_not_imp_left]

@[deprecated find?_replicate_eq_none_iff (since := "2025-03-18")]
abbrev find?_mkVector_eq_none_iff := @find?_replicate_eq_none_iff

@[simp] theorem find?_replicate_eq_some_iff {n : Nat} {a b : α} {p : α → Bool} :
    (replicate n a).find? p = some b ↔ n ≠ 0 ∧ p a ∧ a = b := by
  rw [replicate_eq_mk_replicate, find?_mk]
  simp

@[deprecated find?_replicate_eq_some_iff (since := "2025-03-18")]
abbrev find?_mkVector_eq_some_iff := @find?_replicate_eq_some_iff

@[simp] theorem get_find?_replicate (n : Nat) (a : α) (p : α → Bool) (h) :
    ((replicate n a).find? p).get h = a := by
  simp only [replicate_eq_mk_replicate, find?_mk]
  simp

@[deprecated get_find?_replicate (since := "2025-03-18")]
abbrev get_find?_mkVector := @get_find?_replicate

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

@[simp] theorem findFinIdx?_empty {p : α → Bool} : findFinIdx? p (#v[] : Vector α 0) = none := by simp

@[congr] theorem findFinIdx?_congr {p : α → Bool} {xs : Vector α n} {ys : Vector α n} (w : xs = ys) :
    findFinIdx? p xs = findFinIdx? p ys := by
  subst w
  simp

@[simp] theorem findFinIdx?_subtype {p : α → Prop} {xs : Vector { x // p x } n}
    {f : { x // p x } → Bool} {g : α → Bool} (hf : ∀ x h, f ⟨x, h⟩ = g x) :
    xs.findFinIdx? f = xs.unattach.findFinIdx? g := by
  rcases xs with ⟨xs, rfl⟩
  simp [hf, Function.comp_def]

end Vector
