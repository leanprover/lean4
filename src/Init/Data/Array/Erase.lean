/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.Array.Lemmas
import Init.Data.List.Nat.Erase
import Init.Data.List.Nat.Basic

/-!
# Lemmas about `Array.eraseP`, `Array.erase`, and `Array.eraseIdx`.
-/

-- set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
-- set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace Array

open Nat

/-! ### eraseP -/

@[simp] theorem eraseP_empty : #[].eraseP p = #[] := rfl

theorem eraseP_of_forall_mem_not {xs : Array α} (h : ∀ a, a ∈ xs → ¬p a) : xs.eraseP p = xs := by
  rcases xs with ⟨xs⟩
  simp_all [List.eraseP_of_forall_not]

theorem eraseP_of_forall_getElem_not {xs : Array α} (h : ∀ i, (h : i < xs.size) → ¬p xs[i]) : xs.eraseP p = xs :=
  eraseP_of_forall_mem_not fun a m => by
    rw [mem_iff_getElem] at m
    obtain ⟨i, w, rfl⟩ := m
    exact h i w

@[simp] theorem eraseP_eq_empty_iff {xs : Array α} {p : α → Bool} : xs.eraseP p = #[] ↔ xs = #[] ∨ ∃ x, p x ∧ xs = #[x] := by
  cases xs
  simp

theorem eraseP_ne_empty_iff {xs : Array α} {p : α → Bool} : xs.eraseP p ≠ #[] ↔ xs ≠ #[] ∧ ∀ x, p x → xs ≠ #[x] := by
  simp

theorem exists_of_eraseP {xs : Array α} {a} (hm : a ∈ xs) (hp : p a) :
    ∃ a ys zs, (∀ b ∈ ys, ¬p b) ∧ p a ∧ xs = ys.push a ++ zs ∧ xs.eraseP p = ys ++ zs := by
  rcases xs with ⟨xs⟩
  obtain ⟨a, l₁, l₂, h₁, h₂, rfl, h₃⟩ := List.exists_of_eraseP (by simpa using hm) (hp)
  refine ⟨a, ⟨l₁⟩, ⟨l₂⟩, by simpa using h₁, h₂, by simp, by simpa using h₃⟩

theorem exists_or_eq_self_of_eraseP (p) (xs : Array α) :
    xs.eraseP p = xs ∨
    ∃ a ys zs, (∀ b ∈ ys, ¬p b) ∧ p a ∧ xs = ys.push a ++ zs ∧ xs.eraseP p = ys ++ zs :=
  if h : ∃ a ∈ xs, p a then
    let ⟨_, ha, pa⟩ := h
    .inr (exists_of_eraseP ha pa)
  else
    .inl (eraseP_of_forall_mem_not (h ⟨·, ·, ·⟩))

@[simp] theorem size_eraseP_of_mem {xs : Array α} (al : a ∈ xs) (pa : p a) :
    (xs.eraseP p).size = xs.size - 1 := by
  let ⟨_, ys, zs, _, _, e₁, e₂⟩ := exists_of_eraseP al pa
  rw [e₂]; simp [size_append, e₁]; omega

theorem size_eraseP {xs : Array α} : (xs.eraseP p).size = if xs.any p then xs.size - 1 else xs.size := by
  split <;> rename_i h
  · simp only [any_eq_true] at h
    obtain ⟨i, h, w⟩ := h
    simp [size_eraseP_of_mem (xs := xs) (by simp) w]
  · simp only [any_eq_true] at h
    rw [eraseP_of_forall_getElem_not]
    simp_all

theorem size_eraseP_le (xs : Array α) : (xs.eraseP p).size ≤ xs.size := by
  rcases xs with ⟨xs⟩
  simpa using List.length_eraseP_le xs

theorem le_size_eraseP (xs : Array α) : xs.size - 1 ≤ (xs.eraseP p).size := by
  rcases xs with ⟨xs⟩
  simpa using List.le_length_eraseP xs

theorem mem_of_mem_eraseP {xs : Array α} : a ∈ xs.eraseP p → a ∈ xs := by
  rcases xs with ⟨xs⟩
  simpa using List.mem_of_mem_eraseP

@[simp] theorem mem_eraseP_of_neg {xs : Array α} (pa : ¬p a) : a ∈ xs.eraseP p ↔ a ∈ xs := by
  rcases xs with ⟨xs⟩
  simpa using List.mem_eraseP_of_neg pa

@[simp] theorem eraseP_eq_self_iff {xs : Array α} : xs.eraseP p = xs ↔ ∀ a ∈ xs, ¬ p a := by
  rcases xs with ⟨xs⟩
  simp

theorem eraseP_map (f : β → α) (xs : Array β) : (xs.map f).eraseP p = (xs.eraseP (p ∘ f)).map f := by
  rcases xs with ⟨xs⟩
  simpa using List.eraseP_map f xs

theorem eraseP_filterMap (f : α → Option β) (xs : Array α) :
    (filterMap f xs).eraseP p = filterMap f (xs.eraseP (fun x => match f x with | some y => p y | none => false)) := by
  rcases xs with ⟨xs⟩
  simpa using List.eraseP_filterMap f xs

theorem eraseP_filter (f : α → Bool) (xs : Array α) :
    (filter f xs).eraseP p = filter f (xs.eraseP (fun x => p x && f x)) := by
  rcases xs with ⟨xs⟩
  simpa using List.eraseP_filter f xs

theorem eraseP_append_left {a : α} (pa : p a) {xs : Array α} {ys : Array α} (h : a ∈ xs) :
    (xs ++ ys).eraseP p = xs.eraseP p ++ ys := by
  rcases xs with ⟨xs⟩
  rcases ys with ⟨ys⟩
  simpa using List.eraseP_append_left pa ys (by simpa using h)

theorem eraseP_append_right {xs : Array α} ys (h : ∀ b ∈ xs, ¬p b) :
    (xs ++ ys).eraseP p = xs ++ ys.eraseP p := by
  rcases xs with ⟨xs⟩
  rcases ys with ⟨ys⟩
  simpa using List.eraseP_append_right ys (by simpa using h)

theorem eraseP_append {xs : Array α} {ys : Array α} :
    (xs ++ ys).eraseP p = if xs.any p then xs.eraseP p ++ ys else xs ++ ys.eraseP p := by
  rcases xs with ⟨xs⟩
  rcases ys with ⟨ys⟩
  simp only [List.append_toArray, List.eraseP_toArray, List.eraseP_append, List.any_toArray]
  split <;> simp

theorem eraseP_mkArray (n : Nat) (a : α) (p : α → Bool) :
    (mkArray n a).eraseP p = if p a then mkArray (n - 1) a else mkArray n a := by
  simp only [← List.toArray_replicate, List.eraseP_toArray, List.eraseP_replicate]
  split <;> simp

@[simp] theorem eraseP_mkArray_of_pos {n : Nat} {a : α} (h : p a) :
    (mkArray n a).eraseP p = mkArray (n - 1) a := by
  simp only [← List.toArray_replicate, List.eraseP_toArray]
  simp [h]

@[simp] theorem eraseP_mkArray_of_neg {n : Nat} {a : α} (h : ¬p a) :
    (mkArray n a).eraseP p = mkArray n a := by
  simp only [← List.toArray_replicate, List.eraseP_toArray]
  simp [h]

theorem eraseP_eq_iff {p} {xs : Array α} :
    xs.eraseP p = ys ↔
      ((∀ a ∈ xs, ¬ p a) ∧ xs = ys) ∨
        ∃ a as bs, (∀ b ∈ as, ¬ p b) ∧ p a ∧ xs = as.push a ++ bs ∧ ys = as ++ bs := by
  rcases xs with ⟨l⟩
  rcases ys with ⟨ys⟩
  simp [List.eraseP_eq_iff]
  constructor
  · rintro (h | ⟨a, l₁, h₁, h₂, ⟨l, rfl, rfl⟩⟩)
    · exact Or.inl h
    · exact Or.inr ⟨a, ⟨l₁⟩, by simpa using h₁, h₂, ⟨⟨l⟩, by simp⟩⟩
  · rintro (h | ⟨a, ⟨l₁⟩, h₁, h₂, ⟨⟨l⟩, rfl, rfl⟩⟩)
    · exact Or.inl h
    · exact Or.inr ⟨a, l₁, by simpa using h₁, h₂, ⟨l, by simp⟩⟩

theorem eraseP_comm {xs : Array α} (h : ∀ a ∈ xs, ¬ p a ∨ ¬ q a) :
    (xs.eraseP p).eraseP q = (xs.eraseP q).eraseP p := by
  rcases xs with ⟨xs⟩
  simpa using List.eraseP_comm (by simpa using h)

/-! ### erase -/

section erase
variable [BEq α]

theorem erase_of_not_mem [LawfulBEq α] {a : α} {xs : Array α} (h : a ∉ xs) : xs.erase a = xs := by
  rcases xs with ⟨xs⟩
  simp [List.erase_of_not_mem (by simpa using h)]

theorem erase_eq_eraseP' (a : α) (xs : Array α) : xs.erase a = xs.eraseP (· == a) := by
  rcases xs with ⟨xs⟩
  simp [List.erase_eq_eraseP']

theorem erase_eq_eraseP [LawfulBEq α] (a : α) (xs : Array α) : xs.erase a = xs.eraseP (a == ·) := by
  rcases xs with ⟨xs⟩
  simp [List.erase_eq_eraseP]

@[simp] theorem erase_eq_empty_iff [LawfulBEq α] {xs : Array α} {a : α} :
    xs.erase a = #[] ↔ xs = #[] ∨ xs = #[a] := by
  rcases xs with ⟨xs⟩
  simp [List.erase_eq_nil_iff]

theorem erase_ne_empty_iff [LawfulBEq α] {xs : Array α} {a : α} :
    xs.erase a ≠ #[] ↔ xs ≠ #[] ∧ xs ≠ #[a] := by
  rcases xs with ⟨xs⟩
  simp [List.erase_ne_nil_iff]

theorem exists_erase_eq [LawfulBEq α] {a : α} {xs : Array α} (h : a ∈ xs) :
    ∃ ys zs, a ∉ ys ∧ xs = ys.push a ++ zs ∧ xs.erase a = ys ++ zs := by
  let ⟨_, ys, zs, h₁, e, h₂, h₃⟩ := exists_of_eraseP h (beq_self_eq_true _)
  rw [erase_eq_eraseP]; exact ⟨ys, zs, fun h => h₁ _ h (beq_self_eq_true _), eq_of_beq e ▸ h₂, h₃⟩

@[simp] theorem size_erase_of_mem [LawfulBEq α] {a : α} {xs : Array α} (h : a ∈ xs) :
    (xs.erase a).size = xs.size - 1 := by
  rw [erase_eq_eraseP]; exact size_eraseP_of_mem h (beq_self_eq_true a)

theorem size_erase [LawfulBEq α] (a : α) (xs : Array α) :
    (xs.erase a).size = if a ∈ xs then xs.size - 1 else xs.size := by
  rw [erase_eq_eraseP, size_eraseP]
  congr
  simp [mem_iff_getElem, eq_comm (a := a)]

theorem size_erase_le (a : α) (xs : Array α) : (xs.erase a).size ≤ xs.size := by
  rcases xs with ⟨xs⟩
  simpa using List.length_erase_le a xs

theorem le_size_erase [LawfulBEq α] (a : α) (xs : Array α) : xs.size - 1 ≤ (xs.erase a).size := by
  rcases xs with ⟨xs⟩
  simpa using List.le_length_erase a xs

theorem mem_of_mem_erase {a b : α} {xs : Array α} (h : a ∈ xs.erase b) : a ∈ xs := by
  rcases xs with ⟨xs⟩
  simpa using List.mem_of_mem_erase (by simpa using h)

@[simp] theorem mem_erase_of_ne [LawfulBEq α] {a b : α} {xs : Array α} (ab : a ≠ b) :
    a ∈ xs.erase b ↔ a ∈ xs :=
  erase_eq_eraseP b xs ▸ mem_eraseP_of_neg (mt eq_of_beq ab.symm)

@[simp] theorem erase_eq_self_iff [LawfulBEq α] {xs : Array α} : xs.erase a = xs ↔ a ∉ xs := by
  rw [erase_eq_eraseP', eraseP_eq_self_iff]
  simp [forall_mem_ne']

theorem erase_filter [LawfulBEq α] (f : α → Bool) (xs : Array α) :
    (filter f xs).erase a = filter f (xs.erase a) := by
  rcases xs with ⟨xs⟩
  simpa using List.erase_filter f xs

theorem erase_append_left [LawfulBEq α] {xs : Array α} (ys) (h : a ∈ xs) :
    (xs ++ ys).erase a = xs.erase a ++ ys := by
  rcases xs with ⟨xs⟩
  rcases ys with ⟨ys⟩
  simpa using List.erase_append_left ys (by simpa using h)

theorem erase_append_right [LawfulBEq α] {a : α} {xs : Array α} (ys : Array α) (h : a ∉ xs) :
    (xs ++ ys).erase a = (xs ++ ys.erase a) := by
  rcases xs with ⟨xs⟩
  rcases ys with ⟨ys⟩
  simpa using List.erase_append_right ys (by simpa using h)

theorem erase_append [LawfulBEq α] {a : α} {xs ys : Array α} :
    (xs ++ ys).erase a = if a ∈ xs then xs.erase a ++ ys else xs ++ ys.erase a := by
  rcases xs with ⟨xs⟩
  rcases ys with ⟨ys⟩
  simp only [List.append_toArray, List.erase_toArray, List.erase_append, mem_toArray]
  split <;> simp

theorem erase_mkArray [LawfulBEq α] (n : Nat) (a b : α) :
    (mkArray n a).erase b = if b == a then mkArray (n - 1) a else mkArray n a := by
  simp only [← List.toArray_replicate, List.erase_toArray]
  simp only [List.erase_replicate, beq_iff_eq, List.toArray_replicate]
  split <;> simp

theorem erase_comm [LawfulBEq α] (a b : α) (xs : Array α) :
    (xs.erase a).erase b = (xs.erase b).erase a := by
  rcases xs with ⟨xs⟩
  simpa using List.erase_comm a b xs

theorem erase_eq_iff [LawfulBEq α] {a : α} {xs : Array α} :
    xs.erase a = ys ↔
      (a ∉ xs ∧ xs = ys) ∨
        ∃ as bs, a ∉ as ∧ xs = as.push a ++ bs ∧ ys = as ++ bs := by
  rw [erase_eq_eraseP', eraseP_eq_iff]
  simp only [beq_iff_eq, forall_mem_ne', exists_and_left]
  constructor
  · rintro (⟨h, rfl⟩ | ⟨a', as, h, rfl, bs, rfl, rfl⟩)
    · left; simp_all
    · right; refine ⟨as, h, bs, by simp⟩
  · rintro (⟨h, rfl⟩ | ⟨as, h, bs, rfl, rfl⟩)
    · left; simp_all
    · right; refine ⟨a, as, h, rfl, bs, by simp⟩

@[simp] theorem erase_mkArray_self [LawfulBEq α] {a : α} :
    (mkArray n a).erase a = mkArray (n - 1) a := by
  simp only [← List.toArray_replicate, List.erase_toArray]
  simp [List.erase_replicate]

@[simp] theorem erase_mkArray_ne [LawfulBEq α] {a b : α} (h : !b == a) :
    (mkArray n a).erase b = mkArray n a := by
  rw [erase_of_not_mem]
  simp_all

end erase

/-! ### eraseIdx -/

theorem eraseIdx_eq_take_drop_succ (xs : Array α) (i : Nat) (h) : xs.eraseIdx i = xs.take i ++ xs.drop (i + 1) := by
  rcases xs with ⟨xs⟩
  simp only [List.size_toArray] at h
  simp only [List.eraseIdx_toArray, List.eraseIdx_eq_take_drop_succ, take_eq_extract,
    List.extract_toArray, List.extract_eq_drop_take, Nat.sub_zero, List.drop_zero, drop_eq_extract,
    List.size_toArray, List.append_toArray, mk.injEq, List.append_cancel_left_eq]
  rw [List.take_of_length_le]
  simp

theorem getElem?_eraseIdx (xs : Array α) (i : Nat) (h : i < xs.size) (j : Nat) :
    (xs.eraseIdx i)[j]? = if j < i then xs[j]? else xs[j + 1]? := by
  rcases xs with ⟨xs⟩
  simp [List.getElem?_eraseIdx]

theorem getElem?_eraseIdx_of_lt (xs : Array α) (i : Nat) (h : i < xs.size) (j : Nat) (h' : j < i) :
    (xs.eraseIdx i)[j]? = xs[j]? := by
  rw [getElem?_eraseIdx]
  simp [h']

theorem getElem?_eraseIdx_of_ge (xs : Array α) (i : Nat) (h : i < xs.size) (j : Nat) (h' : i ≤ j) :
    (xs.eraseIdx i)[j]? = xs[j + 1]? := by
  rw [getElem?_eraseIdx]
  simp only [dite_eq_ite, ite_eq_right_iff]
  intro h'
  omega

theorem getElem_eraseIdx (xs : Array α) (i : Nat) (h : i < xs.size) (j : Nat) (h' : j < (xs.eraseIdx i).size) :
    (xs.eraseIdx i)[j] = if h'' : j < i then
        xs[j]
      else
        xs[j + 1]'(by rw [size_eraseIdx] at h'; omega) := by
  apply Option.some.inj
  rw [← getElem?_eq_getElem, getElem?_eraseIdx]
  split <;> simp

@[simp] theorem eraseIdx_eq_empty_iff {xs : Array α} {i : Nat} {h} : xs.eraseIdx i = #[] ↔ xs.size = 1 ∧ i = 0 := by
  rcases xs with ⟨xs⟩
  simp only [List.eraseIdx_toArray, mk.injEq, List.eraseIdx_eq_nil_iff, List.size_toArray,
    or_iff_right_iff_imp]
  rintro rfl
  simp_all

theorem eraseIdx_ne_empty_iff {xs : Array α} {i : Nat} {h} : xs.eraseIdx i ≠ #[] ↔ 2 ≤ xs.size := by
  rcases xs with ⟨_ | ⟨a, (_ | ⟨b, l⟩)⟩⟩
  · simp
  · simp at h
    simp [h]
  · simp

theorem mem_of_mem_eraseIdx {xs : Array α} {i : Nat} {h} {a : α} (h : a ∈ xs.eraseIdx i) : a ∈ xs := by
  rcases xs with ⟨xs⟩
  simpa using List.mem_of_mem_eraseIdx (by simpa using h)

theorem eraseIdx_append_of_lt_size {xs : Array α} {k : Nat} (hk : k < xs.size) (ys : Array α) (h) :
    eraseIdx (xs ++ ys) k = eraseIdx xs k ++ ys := by
  rcases xs with ⟨l⟩
  rcases ys with ⟨l'⟩
  simp at hk
  simp [List.eraseIdx_append_of_lt_length, *]

theorem eraseIdx_append_of_length_le {xs : Array α} {k : Nat} (hk : xs.size ≤ k) (ys : Array α) (h) :
    eraseIdx (xs ++ ys) k = xs ++ eraseIdx ys (k - xs.size) (by simp at h; omega) := by
  rcases xs with ⟨l⟩
  rcases ys with ⟨l'⟩
  simp at hk
  simp [List.eraseIdx_append_of_length_le, *]

theorem eraseIdx_mkArray {n : Nat} {a : α} {k : Nat} {h} :
    (mkArray n a).eraseIdx k = mkArray (n - 1) a := by
  simp at h
  simp only [← List.toArray_replicate, List.eraseIdx_toArray]
  simp [List.eraseIdx_replicate, h]

theorem mem_eraseIdx_iff_getElem {x : α} {xs : Array α} {k} {h} : x ∈ xs.eraseIdx k h ↔ ∃ i w, i ≠ k ∧ xs[i]'w = x := by
  rcases xs with ⟨xs⟩
  simp [List.mem_eraseIdx_iff_getElem, *]

theorem mem_eraseIdx_iff_getElem? {x : α} {xs : Array α} {k} {h} : x ∈ xs.eraseIdx k h ↔ ∃ i ≠ k, xs[i]? = some x := by
  rcases xs with ⟨xs⟩
  simp [List.mem_eraseIdx_iff_getElem?, *]

theorem erase_eq_eraseIdx_of_idxOf [BEq α] [LawfulBEq α] (xs : Array α) (a : α) (i : Nat) (w : xs.idxOf a = i) (h : i < xs.size) :
    xs.erase a = xs.eraseIdx i := by
  rcases xs with ⟨xs⟩
  simp at w
  simp [List.erase_eq_eraseIdx_of_idxOf, *]

theorem getElem_eraseIdx_of_lt (xs : Array α) (i : Nat) (w : i < xs.size) (j : Nat) (h : j < (xs.eraseIdx i).size) (h' : j < i) :
    (xs.eraseIdx i)[j] = xs[j] := by
  rcases xs with ⟨xs⟩
  simp [List.getElem_eraseIdx_of_lt, *]

theorem getElem_eraseIdx_of_ge (xs : Array α) (i : Nat) (w : i < xs.size) (j : Nat) (h : j < (xs.eraseIdx i).size) (h' : i ≤ j) :
    (xs.eraseIdx i)[j] = xs[j + 1]'(by simp at h; omega) := by
  rcases xs with ⟨xs⟩
  simp [List.getElem_eraseIdx_of_ge, *]

theorem eraseIdx_set_eq {xs : Array α} {i : Nat} {a : α} {h : i < xs.size} :
    (xs.set i a).eraseIdx i (by simp; omega) = xs.eraseIdx i := by
  rcases xs with ⟨xs⟩
  simp [List.eraseIdx_set_eq, *]

theorem eraseIdx_set_lt {xs : Array α} {i : Nat} {w : i < xs.size} {j : Nat} {a : α} (h : j < i) :
    (xs.set i a).eraseIdx j (by simp; omega) = (xs.eraseIdx j).set (i - 1) a (by simp; omega) := by
  rcases xs with ⟨xs⟩
  simp [List.eraseIdx_set_lt, *]

theorem eraseIdx_set_gt {xs : Array α} {i : Nat} {j : Nat} {a : α} (h : i < j) {w : j < xs.size} :
    (xs.set i a).eraseIdx j (by simp; omega) = (xs.eraseIdx j).set i a (by simp; omega) := by
  rcases xs with ⟨xs⟩
  simp [List.eraseIdx_set_gt, *]

@[simp] theorem set_getElem_succ_eraseIdx_succ
    {xs : Array α} {i : Nat} (h : i + 1 < xs.size) :
    (xs.eraseIdx (i + 1)).set i xs[i + 1] (by simp; omega) = xs.eraseIdx i := by
  rcases xs with ⟨xs⟩
  simp [List.set_getElem_succ_eraseIdx_succ, *]

end Array
