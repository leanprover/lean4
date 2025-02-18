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

namespace Array

open Nat

/-! ### countP -/
section countP

variable (p q : α → Bool)

@[simp] theorem countP_empty : countP p #[] = 0 := rfl

@[simp] theorem countP_push_of_pos (l) (pa : p a) : countP p (l.push a) = countP p l + 1 := by
  rcases l with ⟨l⟩
  simp_all

@[simp] theorem countP_push_of_neg (l) (pa : ¬p a) : countP p (l.push a) = countP p l := by
  rcases l with ⟨l⟩
  simp_all

theorem countP_push (a : α) (l) : countP p (l.push a) = countP p l + if p a then 1 else 0 := by
  rcases l with ⟨l⟩
  simp_all

@[simp] theorem countP_singleton (a : α) : countP p #[a] = if p a then 1 else 0 := by
  simp [countP_push]

theorem size_eq_countP_add_countP (l) : l.size = countP p l + countP (fun a => ¬p a) l := by
  cases l
  simp [List.length_eq_countP_add_countP (p := p)]

theorem countP_eq_size_filter (l) : countP p l = (filter p l).size := by
  cases l
  simp [List.countP_eq_length_filter]

theorem countP_eq_size_filter' : countP p = size ∘ filter p := by
  funext l
  apply countP_eq_size_filter

theorem countP_le_size : countP p l ≤ l.size := by
  simp only [countP_eq_size_filter]
  apply size_filter_le

@[simp] theorem countP_append (l₁ l₂) : countP p (l₁ ++ l₂) = countP p l₁ + countP p l₂ := by
  cases l₁
  cases l₂
  simp

@[simp] theorem countP_pos_iff {p} : 0 < countP p l ↔ ∃ a ∈ l, p a := by
  cases l
  simp

@[simp] theorem one_le_countP_iff {p} : 1 ≤ countP p l ↔ ∃ a ∈ l, p a :=
  countP_pos_iff

@[simp] theorem countP_eq_zero {p} : countP p l = 0 ↔ ∀ a ∈ l, ¬p a := by
  cases l
  simp

@[simp] theorem countP_eq_size {p} : countP p l = l.size ↔ ∀ a ∈ l, p a := by
  cases l
  simp

theorem countP_mkArray (p : α → Bool) (a : α) (n : Nat) :
    countP p (mkArray n a) = if p a then n else 0 := by
  simp [← List.toArray_replicate, List.countP_replicate]

theorem boole_getElem_le_countP (p : α → Bool) (l : Array α) (i : Nat) (h : i < l.size) :
    (if p l[i] then 1 else 0) ≤ l.countP p := by
  cases l
  simp [List.boole_getElem_le_countP]

theorem countP_set (p : α → Bool) (l : Array α) (i : Nat) (a : α) (h : i < l.size) :
    (l.set i a).countP p = l.countP p - (if p l[i] then 1 else 0) + (if p a then 1 else 0) := by
  cases l
  simp [List.countP_set, h]

theorem countP_filter (l : Array α) :
    countP p (filter q l) = countP (fun a => p a && q a) l := by
  cases l
  simp [List.countP_filter]

@[simp] theorem countP_true : (countP fun (_ : α) => true) = size := by
  funext l
  simp

@[simp] theorem countP_false : (countP fun (_ : α) => false) = Function.const _ 0 := by
  funext l
  simp

@[simp] theorem countP_map (p : β → Bool) (f : α → β) (l : Array α) :
    countP p (map f l) = countP (p ∘ f) l := by
  cases l
  simp

theorem size_filterMap_eq_countP (f : α → Option β) (l : Array α) :
    (filterMap f l).size = countP (fun a => (f a).isSome) l := by
  cases l
  simp [List.length_filterMap_eq_countP]

theorem countP_filterMap (p : β → Bool) (f : α → Option β) (l : Array α) :
    countP p (filterMap f l) = countP (fun a => ((f a).map p).getD false) l := by
  cases l
  simp [List.countP_filterMap]

@[simp] theorem countP_flatten (l : Array (Array α)) :
    countP p l.flatten = (l.map (countP p)).sum := by
  cases l using array₂_induction
  simp [List.countP_flatten, Function.comp_def]

theorem countP_flatMap (p : β → Bool) (l : Array α) (f : α → Array β) :
    countP p (l.flatMap f) = sum (map (countP p ∘ f) l) := by
  cases l
  simp [List.countP_flatMap, Function.comp_def]

@[simp] theorem countP_reverse (l : Array α) : countP p l.reverse = countP p l := by
  cases l
  simp [List.countP_reverse]

variable {p q}

theorem countP_mono_left (h : ∀ x ∈ l, p x → q x) : countP p l ≤ countP q l := by
  cases l
  simpa using List.countP_mono_left (by simpa using h)

theorem countP_congr (h : ∀ x ∈ l, p x ↔ q x) : countP p l = countP q l :=
  Nat.le_antisymm
    (countP_mono_left fun x hx => (h x hx).1)
    (countP_mono_left fun x hx => (h x hx).2)

end countP

/-! ### count -/
section count

variable [BEq α]

@[simp] theorem count_empty (a : α) : count a #[] = 0 := rfl

theorem count_push (a b : α) (l : Array α) :
    count a (l.push b) = count a l + if b == a then 1 else 0 := by
  simp [count, countP_push]

theorem count_eq_countP (a : α) (l : Array α) : count a l = countP (· == a) l := rfl
theorem count_eq_countP' {a : α} : count a = countP (· == a) := by
  funext l
  apply count_eq_countP

theorem count_le_size (a : α) (l : Array α) : count a l ≤ l.size := countP_le_size _

theorem count_le_count_push (a b : α) (l : Array α) : count a l ≤ count a (l.push b) := by
  simp [count_push]

theorem count_singleton (a b : α) : count a #[b] = if b == a then 1 else 0 := by
  simp [count_eq_countP]

@[simp] theorem count_append (a : α) : ∀ l₁ l₂, count a (l₁ ++ l₂) = count a l₁ + count a l₂ :=
  countP_append _

@[simp] theorem count_flatten (a : α) (l : Array (Array α)) :
    count a l.flatten = (l.map (count a)).sum := by
  cases l using array₂_induction
  simp [List.count_flatten, Function.comp_def]

@[simp] theorem count_reverse (a : α) (l : Array α) : count a l.reverse = count a l := by
  cases l
  simp

theorem boole_getElem_le_count (a : α) (l : Array α) (i : Nat) (h : i < l.size) :
    (if l[i] == a then 1 else 0) ≤ l.count a := by
  rw [count_eq_countP]
  apply boole_getElem_le_countP (· == a)

theorem count_set (a b : α) (l : Array α) (i : Nat) (h : i < l.size) :
    (l.set i a).count b = l.count b - (if l[i] == b then 1 else 0) + (if a == b then 1 else 0) := by
  simp [count_eq_countP, countP_set, h]

variable [LawfulBEq α]

@[simp] theorem count_push_self (a : α) (l : Array α) : count a (l.push a) = count a l + 1 := by
  simp [count_push]

@[simp] theorem count_push_of_ne (h : b ≠ a) (l : Array α) : count a (l.push b) = count a l := by
  simp_all [count_push, h]

theorem count_singleton_self (a : α) : count a #[a] = 1 := by simp

@[simp]
theorem count_pos_iff {a : α} {l : Array α} : 0 < count a l ↔ a ∈ l := by
  simp only [count, countP_pos_iff, beq_iff_eq, exists_eq_right]

@[simp] theorem one_le_count_iff {a : α} {l : Array α} : 1 ≤ count a l ↔ a ∈ l :=
  count_pos_iff

theorem count_eq_zero_of_not_mem {a : α} {l : Array α} (h : a ∉ l) : count a l = 0 :=
  Decidable.byContradiction fun h' => h <| count_pos_iff.1 (Nat.pos_of_ne_zero h')

theorem not_mem_of_count_eq_zero {a : α} {l : Array α} (h : count a l = 0) : a ∉ l :=
  fun h' => Nat.ne_of_lt (count_pos_iff.2 h') h.symm

theorem count_eq_zero {l : Array α} : count a l = 0 ↔ a ∉ l :=
  ⟨not_mem_of_count_eq_zero, count_eq_zero_of_not_mem⟩

theorem count_eq_size {l : Array α} : count a l = l.size ↔ ∀ b ∈ l, a = b := by
  rw [count, countP_eq_size]
  refine ⟨fun h b hb => Eq.symm ?_, fun h b hb => ?_⟩
  · simpa using h b hb
  · rw [h b hb, beq_self_eq_true]

@[simp] theorem count_mkArray_self (a : α) (n : Nat) : count a (mkArray n a) = n := by
  simp [← List.toArray_replicate]

theorem count_mkArray (a b : α) (n : Nat) : count a (mkArray n b) = if b == a then n else 0 := by
  simp [← List.toArray_replicate, List.count_replicate]

theorem filter_beq (l : Array α) (a : α) : l.filter (· == a) = mkArray (count a l) a := by
  cases l
  simp [List.filter_beq]

theorem filter_eq {α} [DecidableEq α] (l : Array α) (a : α) : l.filter (· = a) = mkArray (count a l) a :=
  filter_beq l a

theorem mkArray_count_eq_of_count_eq_size {l : Array α} (h : count a l = l.size) :
    mkArray (count a l) a = l := by
  cases l
  rw [← toList_inj]
  simp [List.replicate_count_eq_of_count_eq_length (by simpa using h)]

@[simp] theorem count_filter {l : Array α} (h : p a) : count a (filter p l) = count a l := by
  cases l
  simp [List.count_filter, h]

theorem count_le_count_map [DecidableEq β] (l : Array α) (f : α → β) (x : α) :
    count x l ≤ count (f x) (map f l) := by
  cases l
  simp [List.count_le_count_map, countP_map]

theorem count_filterMap {α} [BEq β] (b : β) (f : α → Option β) (l : Array α) :
    count b (filterMap f l) = countP (fun a => f a == some b) l := by
  cases l
  simp [List.count_filterMap, countP_filterMap]

theorem count_flatMap {α} [BEq β] (l : Array α) (f : α → Array β) (x : β) :
    count x (l.flatMap f) = sum (map (count x ∘ f) l) := by
  simp [count_eq_countP, countP_flatMap, Function.comp_def]

-- FIXME these theorems can be restored once `List.erase` and `Array.erase` have been related.

-- theorem count_erase (a b : α) (l : Array α) : count a (l.erase b) = count a l - if b == a then 1 else 0 := by
--   sorry

-- @[simp] theorem count_erase_self (a : α) (l : Array α) :
--     count a (l.erase a) = count a l - 1 := by rw [count_erase, if_pos (by simp)]

-- @[simp] theorem count_erase_of_ne (ab : a ≠ b) (l : Array α) : count a (l.erase b) = count a l := by
--   rw [count_erase, if_neg (by simpa using ab.symm), Nat.sub_zero]

end count
