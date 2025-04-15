/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.Array.Lemmas
import Init.Data.List.Nat.Count

/-!
# Lemmas about `Array.countP` and `Array.count`.
-/

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace Array

open Nat

/-! ### countP -/
section countP

variable {p q : α → Bool}

@[simp] theorem _root_.List.countP_toArray {l : List α} : countP p l.toArray = l.countP p := by
  simp [countP]
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.foldr_cons, ih, List.countP_cons]
    split <;> simp_all

@[simp] theorem countP_toList {xs : Array α} : xs.toList.countP p = countP p xs := by
  cases xs
  simp

@[simp] theorem countP_empty : countP p #[] = 0 := rfl

@[simp] theorem countP_push_of_pos {xs : Array α} (pa : p a) : countP p (xs.push a) = countP p xs + 1 := by
  rcases xs with ⟨xs⟩
  simp_all

@[simp] theorem countP_push_of_neg {xs : Array α} (pa : ¬p a) : countP p (xs.push a) = countP p xs := by
  rcases xs with ⟨xs⟩
  simp_all

theorem countP_push {a : α} {xs : Array α} : countP p (xs.push a) = countP p xs + if p a then 1 else 0 := by
  rcases xs with ⟨xs⟩
  simp_all

@[simp] theorem countP_singleton {a : α} : countP p #[a] = if p a then 1 else 0 := by
  simp [countP_push]

theorem size_eq_countP_add_countP {xs : Array α} : xs.size = countP p xs + countP (fun a => ¬p a) xs := by
  rcases xs with ⟨xs⟩
  simp [List.length_eq_countP_add_countP (p := p)]

theorem countP_eq_size_filter {xs : Array α} : countP p xs = (filter p xs).size := by
  rcases xs with ⟨xs⟩
  simp [List.countP_eq_length_filter]

theorem countP_eq_size_filter' : countP p = size ∘ filter p := by
  funext xs
  apply countP_eq_size_filter

theorem countP_le_size : countP p xs ≤ xs.size := by
  simp only [countP_eq_size_filter]
  apply size_filter_le

@[simp] theorem countP_append {xs ys : Array α} : countP p (xs ++ ys) = countP p xs + countP p ys := by
  rcases xs with ⟨xs⟩
  rcases ys with ⟨ys⟩
  simp

@[simp] theorem countP_pos_iff {p} : 0 < countP p xs ↔ ∃ a ∈ xs, p a := by
  rcases xs with ⟨xs⟩
  simp

@[simp] theorem one_le_countP_iff {p} : 1 ≤ countP p xs ↔ ∃ a ∈ xs, p a :=
  countP_pos_iff

@[simp] theorem countP_eq_zero {p} : countP p xs = 0 ↔ ∀ a ∈ xs, ¬p a := by
  rcases xs with ⟨xs⟩
  simp

@[simp] theorem countP_eq_size {p} : countP p xs = xs.size ↔ ∀ a ∈ xs, p a := by
  rcases xs with ⟨xs⟩
  simp

theorem countP_replicate {a : α} {n : Nat} : countP p (replicate n a) = if p a then n else 0 := by
  simp [← List.toArray_replicate, List.countP_replicate]

@[deprecated countP_replicate (since := "2025-03-18")]
abbrev countP_mkArray := @countP_replicate

theorem boole_getElem_le_countP {xs : Array α} {i : Nat} (h : i < xs.size) :
    (if p xs[i] then 1 else 0) ≤ xs.countP p := by
  rcases xs with ⟨xs⟩
  simp [List.boole_getElem_le_countP]

theorem countP_set {xs : Array α} {i : Nat} {a : α} (h : i < xs.size) :
    (xs.set i a).countP p = xs.countP p - (if p xs[i] then 1 else 0) + (if p a then 1 else 0) := by
  rcases xs with ⟨xs⟩
  simp [List.countP_set, h]

theorem countP_filter {xs : Array α} :
    countP p (filter q xs) = countP (fun a => p a && q a) xs := by
  rcases xs with ⟨xs⟩
  simp [List.countP_filter]

@[simp] theorem countP_true : (countP fun (_ : α) => true) = size := by
  funext xs
  simp

@[simp] theorem countP_false : (countP fun (_ : α) => false) = Function.const _ 0 := by
  funext xs
  simp

@[simp] theorem countP_map {p : β → Bool} {f : α → β} {xs : Array α} :
    countP p (map f xs) = countP (p ∘ f) xs := by
  rcases xs with ⟨xs⟩
  simp

theorem size_filterMap_eq_countP {f : α → Option β} {xs : Array α} :
    (filterMap f xs).size = countP (fun a => (f a).isSome) xs := by
  rcases xs with ⟨xs⟩
  simp [List.length_filterMap_eq_countP]

theorem countP_filterMap {p : β → Bool} {f : α → Option β} {xs : Array α} :
    countP p (filterMap f xs) = countP (fun a => ((f a).map p).getD false) xs := by
  rcases xs with ⟨xs⟩
  simp [List.countP_filterMap]

@[simp] theorem countP_flatten {xss : Array (Array α)} :
    countP p xss.flatten = (xss.map (countP p)).sum := by
  cases xss using array₂_induction
  simp [List.countP_flatten, Function.comp_def]

theorem countP_flatMap {p : β → Bool} {xs : Array α} {f : α → Array β} :
    countP p (xs.flatMap f) = sum (map (countP p ∘ f) xs) := by
  rcases xs with ⟨xs⟩
  simp [List.countP_flatMap, Function.comp_def]

@[simp] theorem countP_reverse {xs : Array α} : countP p xs.reverse = countP p xs := by
  rcases xs with ⟨xs⟩
  simp [List.countP_reverse]

theorem countP_mono_left (h : ∀ x ∈ xs, p x → q x) : countP p xs ≤ countP q xs := by
  rcases xs with ⟨xs⟩
  simpa using List.countP_mono_left (by simpa using h)

theorem countP_congr (h : ∀ x ∈ xs, p x ↔ q x) : countP p xs = countP q xs :=
  Nat.le_antisymm
    (countP_mono_left fun x hx => (h x hx).1)
    (countP_mono_left fun x hx => (h x hx).2)

end countP

/-! ### count -/
section count

variable [BEq α]

@[simp] theorem _root_.List.count_toArray {l : List α} {a : α} : count a l.toArray = l.count a := by
  simp [count, List.count_eq_countP]

@[simp] theorem count_toList {xs : Array α} {a : α} : xs.toList.count a = xs.count a := by
  cases xs
  simp

@[simp] theorem count_empty {a : α} : count a #[] = 0 := rfl

theorem count_push {a b : α} {xs : Array α} :
    count a (xs.push b) = count a xs + if b == a then 1 else 0 := by
  simp [count, countP_push]

theorem count_eq_countP {a : α} {xs : Array α} : count a xs = countP (· == a) xs := rfl
theorem count_eq_countP' {a : α} : count a = countP (· == a) := by
  funext xs
  apply count_eq_countP

theorem count_le_size {a : α} {xs : Array α} : count a xs ≤ xs.size := countP_le_size

theorem count_le_count_push {a b : α} {xs : Array α} : count a xs ≤ count a (xs.push b) := by
  simp [count_push]

theorem count_singleton {a b : α} : count a #[b] = if b == a then 1 else 0 := by
  simp [count_eq_countP]

@[simp] theorem count_append {a : α} {xs ys : Array α} : count a (xs ++ ys) = count a xs + count a ys :=
  countP_append

@[simp] theorem count_flatten {a : α} {xss : Array (Array α)} :
    count a xss.flatten = (xss.map (count a)).sum := by
  cases xss using array₂_induction
  simp [List.count_flatten, Function.comp_def]

@[simp] theorem count_reverse {a : α} {xs : Array α} : count a xs.reverse = count a xs := by
  rcases xs with ⟨xs⟩
  simp

theorem boole_getElem_le_count {xs : Array α} {i : Nat} {a : α} (h : i < xs.size) :
    (if xs[i] == a then 1 else 0) ≤ xs.count a := by
  rw [count_eq_countP]
  apply boole_getElem_le_countP (p := (· == a))

theorem count_set {xs : Array α} {i : Nat} {a b : α} (h : i < xs.size) :
    (xs.set i a).count b = xs.count b - (if xs[i] == b then 1 else 0) + (if a == b then 1 else 0) := by
  simp [count_eq_countP, countP_set, h]

variable [LawfulBEq α]

@[simp] theorem count_push_self {a : α} {xs : Array α} : count a (xs.push a) = count a xs + 1 := by
  simp [count_push]

@[simp] theorem count_push_of_ne {xs : Array α} (h : b ≠ a) : count a (xs.push b) = count a xs := by
  simp_all [count_push, h]

theorem count_singleton_self {a : α} : count a #[a] = 1 := by simp

@[simp]
theorem count_pos_iff {a : α} {xs : Array α} : 0 < count a xs ↔ a ∈ xs := by
  simp only [count, countP_pos_iff, beq_iff_eq, exists_eq_right]

@[simp] theorem one_le_count_iff {a : α} {xs : Array α} : 1 ≤ count a xs ↔ a ∈ xs :=
  count_pos_iff

theorem count_eq_zero_of_not_mem {a : α} {xs : Array α} (h : a ∉ xs) : count a xs = 0 :=
  Decidable.byContradiction fun h' => h <| count_pos_iff.1 (Nat.pos_of_ne_zero h')

theorem not_mem_of_count_eq_zero {a : α} {xs : Array α} (h : count a xs = 0) : a ∉ xs :=
  fun h' => Nat.ne_of_lt (count_pos_iff.2 h') h.symm

theorem count_eq_zero {xs : Array α} : count a xs = 0 ↔ a ∉ xs :=
  ⟨not_mem_of_count_eq_zero, count_eq_zero_of_not_mem⟩

theorem count_eq_size {xs : Array α} : count a xs = xs.size ↔ ∀ b ∈ xs, a = b := by
  rw [count, countP_eq_size]
  refine ⟨fun h b hb => Eq.symm ?_, fun h b hb => ?_⟩
  · simpa using h b hb
  · rw [h b hb, beq_self_eq_true]

@[simp] theorem count_replicate_self {a : α} {n : Nat} : count a (replicate n a) = n := by
  simp [← List.toArray_replicate]

@[deprecated count_replicate_self (since := "2025-03-18")]
abbrev count_mkArray_self := @count_replicate_self

theorem count_replicate {a b : α} {n : Nat} : count a (replicate n b) = if b == a then n else 0 := by
  simp [← List.toArray_replicate, List.count_replicate]

@[deprecated count_replicate (since := "2025-03-18")]
abbrev count_mkArray := @count_replicate

theorem filter_beq {xs : Array α} (a : α) : xs.filter (· == a) = replicate (count a xs) a := by
  rcases xs with ⟨xs⟩
  simp [List.filter_beq]

theorem filter_eq {α} [DecidableEq α] {xs : Array α} (a : α) : xs.filter (· = a) = replicate (count a xs) a :=
  filter_beq a

theorem replicate_count_eq_of_count_eq_size {xs : Array α} (h : count a xs = xs.size) :
    replicate (count a xs) a = xs := by
  rcases xs with ⟨xs⟩
  rw [← toList_inj]
  simp [List.replicate_count_eq_of_count_eq_length (by simpa using h)]

@[deprecated replicate_count_eq_of_count_eq_size (since := "2025-03-18")]
abbrev mkArray_count_eq_of_count_eq_size := @replicate_count_eq_of_count_eq_size

@[simp] theorem count_filter {xs : Array α} (h : p a) : count a (filter p xs) = count a xs := by
  rcases xs with ⟨xs⟩
  simp [List.count_filter, h]

theorem count_le_count_map [DecidableEq β] {xs : Array α} {f : α → β} {x : α} :
    count x xs ≤ count (f x) (map f xs) := by
  rcases xs with ⟨xs⟩
  simp [List.count_le_count_map, countP_map]

theorem count_filterMap {α} [BEq β] {b : β} {f : α → Option β} {xs : Array α} :
    count b (filterMap f xs) = countP (fun a => f a == some b) xs := by
  rcases xs with ⟨xs⟩
  simp [List.count_filterMap, countP_filterMap]

theorem count_flatMap {α} [BEq β] {xs : Array α} {f : α → Array β} {x : β} :
    count x (xs.flatMap f) = sum (map (count x ∘ f) xs) := by
  rcases xs with ⟨xs⟩
  simp [List.count_flatMap, countP_flatMap, Function.comp_def]

theorem countP_replace {a b : α} {xs : Array α} {p : α → Bool} :
    (xs.replace a b).countP p =
      if xs.contains a then xs.countP p + (if p b then 1 else 0) - (if p a then 1 else 0) else xs.countP p := by
  rcases xs with ⟨xs⟩
  simp [List.countP_replace]

theorem count_replace {a b c : α} {xs : Array α} :
    (xs.replace a b).count c =
      if xs.contains a then xs.count c + (if b == c then 1 else 0) - (if a == c then 1 else 0) else xs.count c := by
  simp [count_eq_countP, countP_replace]

theorem count_erase (a b : α) (xs : Array α) : count a (xs.erase b) = count a xs - if b == a then 1 else 0 := by
  rcases xs with ⟨l⟩
  simp [List.count_erase]

@[simp] theorem count_erase_self (a : α) (xs : Array α) :
    count a (xs.erase a) = count a xs - 1 := by rw [count_erase, if_pos (by simp)]

@[simp] theorem count_erase_of_ne (ab : a ≠ b) (xs : Array α) : count a (xs.erase b) = count a xs := by
  rw [count_erase, if_neg (by simpa using ab.symm), Nat.sub_zero]

end count
