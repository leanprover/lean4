/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.Array.Count
import Init.Data.Vector.Lemmas

/-!
# Lemmas about `Vector.countP` and `Vector.count`.
-/

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace Vector

open Nat

/-! ### countP -/
section countP

variable (p q : α → Bool)

@[simp] theorem countP_empty : countP p #v[] = 0 := rfl

@[simp] theorem countP_push_of_pos (xs : Vector α n) (pa : p a) : countP p (xs.push a) = countP p xs + 1 := by
  rcases xs with ⟨xs, rfl⟩
  simp_all

@[simp] theorem countP_push_of_neg (xs : Vector α n) (pa : ¬p a) : countP p (xs.push a) = countP p xs := by
  rcases xs with ⟨xs, rfl⟩
  simp_all

theorem countP_push (a : α) (xs : Vector α n) : countP p (xs.push a) = countP p xs + if p a then 1 else 0 := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.countP_push]

@[simp] theorem countP_singleton (a : α) : countP p #v[a] = if p a then 1 else 0 := by
  simp [countP_push]

theorem size_eq_countP_add_countP (xs : Vector α n) : n = countP p xs + countP (fun a => ¬p a) xs := by
  rcases xs with ⟨xs, rfl⟩
  simp [List.length_eq_countP_add_countP (p := p)]

theorem countP_le_size {xs : Vector α n} : countP p xs ≤ n := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.countP_le_size (p := p)]

@[simp] theorem countP_append (xs : Vector α n) (ys : Vector α m) : countP p (xs ++ ys) = countP p xs + countP p ys := by
  cases xs
  cases ys
  simp

@[simp] theorem countP_pos_iff {p} : 0 < countP p xs ↔ ∃ a ∈ xs, p a := by
  cases xs
  simp

@[simp] theorem one_le_countP_iff {p} : 1 ≤ countP p xs ↔ ∃ a ∈ xs, p a :=
  countP_pos_iff

@[simp] theorem countP_eq_zero {p} : countP p xs = 0 ↔ ∀ a ∈ xs, ¬p a := by
  cases xs
  simp

@[simp] theorem countP_eq_size {p} : countP p xs = xs.size ↔ ∀ a ∈ xs, p a := by
  cases xs
  simp

@[simp] theorem countP_cast (p : α → Bool) (xs : Vector α n) : countP p (xs.cast h) = countP p xs := by
  rcases xs with ⟨xs, rfl⟩
  simp

theorem countP_mkVector (p : α → Bool) (a : α) (n : Nat) :
    countP p (mkVector n a) = if p a then n else 0 := by
  simp only [mkVector_eq_mk_mkArray, countP_cast, countP_mk]
  simp [Array.countP_mkArray]

theorem boole_getElem_le_countP (p : α → Bool) (xs : Vector α n) (i : Nat) (h : i < n) :
    (if p xs[i] then 1 else 0) ≤ xs.countP p := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.boole_getElem_le_countP]

theorem countP_set (p : α → Bool) (xs : Vector α n) (i : Nat) (a : α) (h : i < n) :
    (xs.set i a).countP p = xs.countP p - (if p xs[i] then 1 else 0) + (if p a then 1 else 0) := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.countP_set, h]

@[simp] theorem countP_true : (countP fun (_ : α) => true) = (fun (_ : Vector α n) => n) := by
  funext xs
  rw [countP]
  simp only [Array.countP_true, xs.2]

@[simp] theorem countP_false : (countP fun (_ : α) => false) = (fun (_ : Vector α n) => 0) := by
  funext xs
  simp

@[simp] theorem countP_map (p : β → Bool) (f : α → β) (xs : Vector α n) :
    countP p (map f xs) = countP (p ∘ f) xs := by
  rcases xs with ⟨xs, rfl⟩
  simp

set_option linter.listVariables false in -- This can probably be removed later.
@[simp] theorem countP_flatten (xss : Vector (Vector α m) n) :
    countP p xss.flatten = (xss.map (countP p)).sum := by
  rcases xss with ⟨xss, rfl⟩
  simp [Function.comp_def]

theorem countP_flatMap (p : β → Bool) (xs : Vector α n) (f : α → Vector β m) :
    countP p (xs.flatMap f) = (map (countP p ∘ f) xs).sum := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.countP_flatMap, Function.comp_def]

@[simp] theorem countP_reverse (xs : Vector α n) : countP p xs.reverse = countP p xs := by
  rcases xs with ⟨xs, rfl⟩
  simp

variable {p q}

theorem countP_mono_left (h : ∀ x ∈ xs, p x → q x) : countP p xs ≤ countP q xs := by
  rcases xs with ⟨xs, rfl⟩
  simpa using Array.countP_mono_left (by simpa using h)

theorem countP_congr (h : ∀ x ∈ xs, p x ↔ q x) : countP p xs = countP q xs :=
  Nat.le_antisymm
    (countP_mono_left fun x hx => (h x hx).1)
    (countP_mono_left fun x hx => (h x hx).2)

end countP

/-! ### count -/
section count

variable [BEq α]

@[simp] theorem count_empty (a : α) : count a #v[] = 0 := rfl

theorem count_push (a b : α) (xs : Vector α n) :
    count a (xs.push b) = count a xs + if b == a then 1 else 0 := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.count_push]

theorem count_eq_countP (a : α) (xs : Vector α n) : count a xs = countP (· == a) xs := rfl

theorem count_eq_countP' {a : α} : count (n := n) a = countP (· == a) := by
  funext xs
  apply count_eq_countP

theorem count_le_size (a : α) (xs : Vector α n) : count a xs ≤ n := countP_le_size _

theorem count_le_count_push (a b : α) (xs : Vector α n) : count a xs ≤ count a (xs.push b) := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.count_push]

@[simp] theorem count_singleton (a b : α) : count a #v[b] = if b == a then 1 else 0 := by
  simp [count_eq_countP]

@[simp] theorem count_append (a : α) (xs : Vector α n) (ys : Vector α m) :
    count a (xs ++ ys) = count a xs + count a ys :=
  countP_append ..

set_option linter.listVariables false in -- This can probably be removed later.
@[simp] theorem count_flatten (a : α) (xss : Vector (Vector α m) n) :
    count a xss.flatten = (xss.map (count a)).sum := by
  rcases xss with ⟨xss, rfl⟩
  simp [Array.count_flatten, Function.comp_def]

@[simp] theorem count_reverse (a : α) (xs : Vector α n) : count a xs.reverse = count a xs := by
  rcases xs with ⟨xs, rfl⟩
  simp

theorem boole_getElem_le_count (a : α) (xs : Vector α n) (i : Nat) (h : i < n) :
    (if xs[i] == a then 1 else 0) ≤ xs.count a := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.boole_getElem_le_count, h]

theorem count_set (a b : α) (xs : Vector α n) (i : Nat) (h : i < n) :
    (xs.set i a).count b = xs.count b - (if xs[i] == b then 1 else 0) + (if a == b then 1 else 0) := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.count_set, h]

@[simp] theorem count_cast (xs : Vector α n) : (xs.cast h).count a = xs.count a := by
  rcases xs with ⟨xs, rfl⟩
  simp

variable [LawfulBEq α]

@[simp] theorem count_push_self (a : α) (xs : Vector α n) : count a (xs.push a) = count a xs + 1 := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.count_push_self]

@[simp] theorem count_push_of_ne (h : b ≠ a) (xs : Vector α n) : count a (xs.push b) = count a xs := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.count_push_of_ne, h]

theorem count_singleton_self (a : α) : count a #v[a] = 1 := by simp

@[simp]
theorem count_pos_iff {a : α} {xs : Vector α n} : 0 < count a xs ↔ a ∈ xs := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.count_pos_iff, beq_iff_eq, exists_eq_right]

@[simp] theorem one_le_count_iff {a : α} {xs : Vector α n} : 1 ≤ count a xs ↔ a ∈ xs :=
  count_pos_iff

theorem count_eq_zero_of_not_mem {a : α} {xs : Vector α n} (h : a ∉ xs) : count a xs = 0 :=
  Decidable.byContradiction fun h' => h <| count_pos_iff.1 (Nat.pos_of_ne_zero h')

theorem not_mem_of_count_eq_zero {a : α} {xs : Vector α n} (h : count a xs = 0) : a ∉ xs :=
  fun h' => Nat.ne_of_lt (count_pos_iff.2 h') h.symm

theorem count_eq_zero {xs : Vector α n} : count a xs = 0 ↔ a ∉ xs :=
  ⟨not_mem_of_count_eq_zero, count_eq_zero_of_not_mem⟩

theorem count_eq_size {xs : Vector α n} : count a xs = xs.size ↔ ∀ b ∈ xs, a = b := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.count_eq_size]

@[simp] theorem count_mkVector_self (a : α) (n : Nat) : count a (mkVector n a) = n := by
  simp only [mkVector_eq_mk_mkArray, count_cast, count_mk]
  simp

theorem count_mkVector (a b : α) (n : Nat) : count a (mkVector n b) = if b == a then n else 0 := by
  simp only [mkVector_eq_mk_mkArray, count_cast, count_mk]
  simp [Array.count_mkArray]

theorem count_le_count_map [DecidableEq β] (xs : Vector α n) (f : α → β) (x : α) :
    count x xs ≤ count (f x) (map f xs) := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.count_le_count_map]

theorem count_flatMap {α} [BEq β] (xs : Vector α n) (f : α → Vector β m) (x : β) :
    count x (xs.flatMap f) = (map (count x ∘ f) xs).sum := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.count_flatMap, Function.comp_def]

end count
