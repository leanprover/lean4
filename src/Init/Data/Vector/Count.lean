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

namespace Vector

open Nat

/-! ### countP -/
section countP

variable (p q : α → Bool)

@[simp] theorem countP_empty : countP p #v[] = 0 := rfl

@[simp] theorem countP_push_of_pos (l : Vector α n) (pa : p a) : countP p (l.push a) = countP p l + 1 := by
  rcases l with ⟨l⟩
  simp_all

@[simp] theorem countP_push_of_neg (l : Vector α n) (pa : ¬p a) : countP p (l.push a) = countP p l := by
  rcases l with ⟨l, rfl⟩
  simp_all

theorem countP_push (a : α) (l : Vector α n) : countP p (l.push a) = countP p l + if p a then 1 else 0 := by
  rcases l with ⟨l, rfl⟩
  simp [Array.countP_push]

@[simp] theorem countP_singleton (a : α) : countP p #v[a] = if p a then 1 else 0 := by
  simp [countP_push]

theorem size_eq_countP_add_countP (l : Vector α n) : n = countP p l + countP (fun a => ¬p a) l := by
  rcases l with ⟨l, rfl⟩
  simp [List.length_eq_countP_add_countP (p := p)]

theorem countP_le_size {l : Vector α n} : countP p l ≤ n := by
  rcases l with ⟨l, rfl⟩
  simp [Array.countP_le_size (p := p)]

@[simp] theorem countP_append (l₁ : Vector α n) (l₂ : Vector α m) : countP p (l₁ ++ l₂) = countP p l₁ + countP p l₂ := by
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

@[simp] theorem countP_cast (p : α → Bool) (l : Vector α n) : countP p (l.cast h) = countP p l := by
  rcases l with ⟨l, rfl⟩
  simp

theorem countP_mkVector (p : α → Bool) (a : α) (n : Nat) :
    countP p (mkVector n a) = if p a then n else 0 := by
  simp only [mkVector_eq_mk_mkArray, countP_cast, countP_mk]
  simp [Array.countP_mkArray]

theorem boole_getElem_le_countP (p : α → Bool) (l : Vector α n) (i : Nat) (h : i < n) :
    (if p l[i] then 1 else 0) ≤ l.countP p := by
  rcases l with ⟨l, rfl⟩
  simp [Array.boole_getElem_le_countP]

theorem countP_set (p : α → Bool) (l : Vector α n) (i : Nat) (a : α) (h : i < n) :
    (l.set i a).countP p = l.countP p - (if p l[i] then 1 else 0) + (if p a then 1 else 0) := by
  cases l
  simp [Array.countP_set, h]

@[simp] theorem countP_true : (countP fun (_ : α) => true) = (fun (_ : Vector α n) => n) := by
  funext l
  rw [countP]
  simp only [Array.countP_true, l.2]

@[simp] theorem countP_false : (countP fun (_ : α) => false) = (fun (_ : Vector α n) => 0) := by
  funext l
  simp

@[simp] theorem countP_map (p : β → Bool) (f : α → β) (l : Vector α n) :
    countP p (map f l) = countP (p ∘ f) l := by
  rcases l with ⟨l, rfl⟩
  simp

@[simp] theorem countP_flatten (l : Vector (Vector α m) n) :
    countP p l.flatten = (l.map (countP p)).sum := by
  rcases l with ⟨l, rfl⟩
  simp [Function.comp_def]

theorem countP_flatMap (p : β → Bool) (l : Vector α n) (f : α → Vector β m) :
    countP p (l.flatMap f) = (map (countP p ∘ f) l).sum := by
  rcases l with ⟨l, rfl⟩
  simp [Array.countP_flatMap, Function.comp_def]

@[simp] theorem countP_reverse (l : Vector α n) : countP p l.reverse = countP p l := by
  cases l
  simp

variable {p q}

theorem countP_mono_left (h : ∀ x ∈ l, p x → q x) : countP p l ≤ countP q l := by
  cases l
  simpa using Array.countP_mono_left (by simpa using h)

theorem countP_congr (h : ∀ x ∈ l, p x ↔ q x) : countP p l = countP q l :=
  Nat.le_antisymm
    (countP_mono_left fun x hx => (h x hx).1)
    (countP_mono_left fun x hx => (h x hx).2)

end countP

/-! ### count -/
section count

variable [BEq α]

@[simp] theorem count_empty (a : α) : count a #v[] = 0 := rfl

theorem count_push (a b : α) (l : Vector α n) :
    count a (l.push b) = count a l + if b == a then 1 else 0 := by
  rcases l with ⟨l, rfl⟩
  simp [Array.count_push]

theorem count_eq_countP (a : α) (l : Vector α n) : count a l = countP (· == a) l := rfl

theorem count_eq_countP' {a : α} : count (n := n) a = countP (· == a) := by
  funext l
  apply count_eq_countP

theorem count_le_size (a : α) (l : Vector α n) : count a l ≤ n := countP_le_size _

theorem count_le_count_push (a b : α) (l : Vector α n) : count a l ≤ count a (l.push b) := by
  rcases l with ⟨l, rfl⟩
  simp [Array.count_push]

@[simp] theorem count_singleton (a b : α) : count a #v[b] = if b == a then 1 else 0 := by
  simp [count_eq_countP]

@[simp] theorem count_append (a : α) (l₁ : Vector α n) (l₂ : Vector α m) :
    count a (l₁ ++ l₂) = count a l₁ + count a l₂ :=
  countP_append ..

@[simp] theorem count_flatten (a : α) (l : Vector (Vector α m) n) :
    count a l.flatten = (l.map (count a)).sum := by
  rcases l with ⟨l, rfl⟩
  simp [Array.count_flatten, Function.comp_def]

@[simp] theorem count_reverse (a : α) (l : Vector α n) : count a l.reverse = count a l := by
  rcases l with ⟨l, rfl⟩
  simp

theorem boole_getElem_le_count (a : α) (l : Vector α n) (i : Nat) (h : i < n) :
    (if l[i] == a then 1 else 0) ≤ l.count a := by
  rcases l with ⟨l, rfl⟩
  simp [Array.boole_getElem_le_count, h]

theorem count_set (a b : α) (l : Vector α n) (i : Nat) (h : i < n) :
    (l.set i a).count b = l.count b - (if l[i] == b then 1 else 0) + (if a == b then 1 else 0) := by
  rcases l with ⟨l, rfl⟩
  simp [Array.count_set, h]

@[simp] theorem count_cast (l : Vector α n) : (l.cast h).count a = l.count a := by
  rcases l with ⟨l, rfl⟩
  simp

variable [LawfulBEq α]

@[simp] theorem count_push_self (a : α) (l : Vector α n) : count a (l.push a) = count a l + 1 := by
  rcases l with ⟨l, rfl⟩
  simp [Array.count_push_self]

@[simp] theorem count_push_of_ne (h : b ≠ a) (l : Vector α n) : count a (l.push b) = count a l := by
  rcases l with ⟨l, rfl⟩
  simp [Array.count_push_of_ne, h]

theorem count_singleton_self (a : α) : count a #v[a] = 1 := by simp

@[simp]
theorem count_pos_iff {a : α} {l : Vector α n} : 0 < count a l ↔ a ∈ l := by
  rcases l with ⟨l, rfl⟩
  simp [Array.count_pos_iff, beq_iff_eq, exists_eq_right]

@[simp] theorem one_le_count_iff {a : α} {l : Vector α n} : 1 ≤ count a l ↔ a ∈ l :=
  count_pos_iff

theorem count_eq_zero_of_not_mem {a : α} {l : Vector α n} (h : a ∉ l) : count a l = 0 :=
  Decidable.byContradiction fun h' => h <| count_pos_iff.1 (Nat.pos_of_ne_zero h')

theorem not_mem_of_count_eq_zero {a : α} {l : Vector α n} (h : count a l = 0) : a ∉ l :=
  fun h' => Nat.ne_of_lt (count_pos_iff.2 h') h.symm

theorem count_eq_zero {l : Vector α n} : count a l = 0 ↔ a ∉ l :=
  ⟨not_mem_of_count_eq_zero, count_eq_zero_of_not_mem⟩

theorem count_eq_size {l : Vector α n} : count a l = l.size ↔ ∀ b ∈ l, a = b := by
  rcases l with ⟨l, rfl⟩
  simp [Array.count_eq_size]

@[simp] theorem count_mkVector_self (a : α) (n : Nat) : count a (mkVector n a) = n := by
  simp only [mkVector_eq_mk_mkArray, count_cast, count_mk]
  simp

theorem count_mkVector (a b : α) (n : Nat) : count a (mkVector n b) = if b == a then n else 0 := by
  simp only [mkVector_eq_mk_mkArray, count_cast, count_mk]
  simp [Array.count_mkArray]

theorem count_le_count_map [DecidableEq β] (l : Vector α n) (f : α → β) (x : α) :
    count x l ≤ count (f x) (map f l) := by
  rcases l with ⟨l, rfl⟩
  simp [Array.count_le_count_map]

theorem count_flatMap {α} [BEq β] (l : Vector α n) (f : α → Vector β m) (x : β) :
    count x (l.flatMap f) = (map (count x ∘ f) l).sum := by
  rcases l with ⟨l, rfl⟩
  simp [Array.count_flatMap, Function.comp_def]

end count
