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

namespace Array

open Nat

/-! ### eraseP -/

@[simp] theorem eraseP_empty : #[].eraseP p = #[] := rfl

theorem eraseP_of_forall_mem_not {l : Array α} (h : ∀ a, a ∈ l → ¬p a) : l.eraseP p = l := by
  cases l
  simp_all [List.eraseP_of_forall_not]

theorem eraseP_of_forall_getElem_not {l : Array α} (h : ∀ i, (h : i < l.size) → ¬p l[i]) : l.eraseP p = l :=
  eraseP_of_forall_mem_not fun a m => by
    rw [mem_iff_getElem] at m
    obtain ⟨i, w, rfl⟩ := m
    exact h i w

@[simp] theorem eraseP_eq_empty_iff {xs : Array α} {p : α → Bool} : xs.eraseP p = #[] ↔ xs = #[] ∨ ∃ x, p x ∧ xs = #[x] := by
  cases xs
  simp

theorem eraseP_ne_empty_iff {xs : Array α} {p : α → Bool} : xs.eraseP p ≠ #[] ↔ xs ≠ #[] ∧ ∀ x, p x → xs ≠ #[x] := by
  simp

theorem exists_of_eraseP {l : Array α} {a} (hm : a ∈ l) (hp : p a) :
    ∃ a l₁ l₂, (∀ b ∈ l₁, ¬p b) ∧ p a ∧ l = l₁.push a ++ l₂ ∧ l.eraseP p = l₁ ++ l₂ := by
  rcases l with ⟨l⟩
  obtain ⟨a, l₁, l₂, h₁, h₂, rfl, h₃⟩ := List.exists_of_eraseP (by simpa using hm) (hp)
  refine ⟨a, ⟨l₁⟩, ⟨l₂⟩, by simpa using h₁, h₂, by simp, by simpa using h₃⟩

theorem exists_or_eq_self_of_eraseP (p) (l : Array α) :
    l.eraseP p = l ∨
    ∃ a l₁ l₂, (∀ b ∈ l₁, ¬p b) ∧ p a ∧ l = l₁.push a ++ l₂ ∧ l.eraseP p = l₁ ++ l₂ :=
  if h : ∃ a ∈ l, p a then
    let ⟨_, ha, pa⟩ := h
    .inr (exists_of_eraseP ha pa)
  else
    .inl (eraseP_of_forall_mem_not (h ⟨·, ·, ·⟩))

@[simp] theorem size_eraseP_of_mem {l : Array α} (al : a ∈ l) (pa : p a) :
    (l.eraseP p).size = l.size - 1 := by
  let ⟨_, l₁, l₂, _, _, e₁, e₂⟩ := exists_of_eraseP al pa
  rw [e₂]; simp [size_append, e₁]; omega

theorem size_eraseP {l : Array α} : (l.eraseP p).size = if l.any p then l.size - 1 else l.size := by
  split <;> rename_i h
  · simp only [any_eq_true] at h
    obtain ⟨i, h, w⟩ := h
    simp [size_eraseP_of_mem (l := l) (by simp) w]
  · simp only [any_eq_true] at h
    rw [eraseP_of_forall_getElem_not]
    simp_all

theorem size_eraseP_le (l : Array α) : (l.eraseP p).size ≤ l.size := by
  rcases l with ⟨l⟩
  simpa using List.length_eraseP_le l

theorem le_size_eraseP (l : Array α) : l.size - 1 ≤ (l.eraseP p).size := by
  rcases l with ⟨l⟩
  simpa using List.le_length_eraseP l

theorem mem_of_mem_eraseP {l : Array α} : a ∈ l.eraseP p → a ∈ l := by
  rcases l with ⟨l⟩
  simpa using List.mem_of_mem_eraseP

@[simp] theorem mem_eraseP_of_neg {l : Array α} (pa : ¬p a) : a ∈ l.eraseP p ↔ a ∈ l := by
  rcases l with ⟨l⟩
  simpa using List.mem_eraseP_of_neg pa

@[simp] theorem eraseP_eq_self_iff {p} {l : Array α} : l.eraseP p = l ↔ ∀ a ∈ l, ¬ p a := by
  rcases l with ⟨l⟩
  simp

theorem eraseP_map (f : β → α) (l : Array β) : (map f l).eraseP p = map f (l.eraseP (p ∘ f)) := by
  rcases l with ⟨l⟩
  simpa using List.eraseP_map f l

theorem eraseP_filterMap (f : α → Option β) (l : Array α) :
    (filterMap f l).eraseP p = filterMap f (l.eraseP (fun x => match f x with | some y => p y | none => false)) := by
  rcases l with ⟨l⟩
  simpa using List.eraseP_filterMap f l

theorem eraseP_filter (f : α → Bool) (l : Array α) :
    (filter f l).eraseP p = filter f (l.eraseP (fun x => p x && f x)) := by
  rcases l with ⟨l⟩
  simpa using List.eraseP_filter f l

theorem eraseP_append_left {a : α} (pa : p a) {l₁ : Array α} l₂ (h : a ∈ l₁) :
    (l₁ ++ l₂).eraseP p = l₁.eraseP p ++ l₂ := by
  rcases l₁ with ⟨l₁⟩
  rcases l₂ with ⟨l₂⟩
  simpa using List.eraseP_append_left pa l₂ (by simpa using h)

theorem eraseP_append_right {l₁ : Array α} l₂ (h : ∀ b ∈ l₁, ¬p b) :
    (l₁ ++ l₂).eraseP p = l₁ ++ l₂.eraseP p := by
  rcases l₁ with ⟨l₁⟩
  rcases l₂ with ⟨l₂⟩
  simpa using List.eraseP_append_right l₂ (by simpa using h)

theorem eraseP_append (l₁ l₂ : Array α) :
    (l₁ ++ l₂).eraseP p = if l₁.any p then l₁.eraseP p ++ l₂ else l₁ ++ l₂.eraseP p := by
  rcases l₁ with ⟨l₁⟩
  rcases l₂ with ⟨l₂⟩
  simp only [List.append_toArray, List.eraseP_toArray, List.eraseP_append l₁ l₂, List.any_toArray']
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

theorem eraseP_eq_iff {p} {l : Array α} :
    l.eraseP p = l' ↔
      ((∀ a ∈ l, ¬ p a) ∧ l = l') ∨
        ∃ a l₁ l₂, (∀ b ∈ l₁, ¬ p b) ∧ p a ∧ l = l₁.push a ++ l₂ ∧ l' = l₁ ++ l₂ := by
  rcases l with ⟨l⟩
  rcases l' with ⟨l'⟩
  simp [List.eraseP_eq_iff]
  constructor
  · rintro (h | ⟨a, l₁, h₁, h₂, ⟨x, rfl, rfl⟩⟩)
    · exact Or.inl h
    · exact Or.inr ⟨a, ⟨l₁⟩, by simpa using h₁, h₂, ⟨⟨x⟩, by simp⟩⟩
  · rintro (h | ⟨a, ⟨l₁⟩, h₁, h₂, ⟨⟨x⟩, rfl, rfl⟩⟩)
    · exact Or.inl h
    · exact Or.inr ⟨a, l₁, by simpa using h₁, h₂, ⟨x, by simp⟩⟩

theorem eraseP_comm {l : Array α} (h : ∀ a ∈ l, ¬ p a ∨ ¬ q a) :
    (l.eraseP p).eraseP q = (l.eraseP q).eraseP p := by
  rcases l with ⟨l⟩
  simpa using List.eraseP_comm (by simpa using h)

/-! ### erase -/

section erase
variable [BEq α]

theorem erase_of_not_mem [LawfulBEq α] {a : α} {l : Array α} (h : a ∉ l) : l.erase a = l := by
  rcases l with ⟨l⟩
  simp [List.erase_of_not_mem (by simpa using h)]

theorem erase_eq_eraseP' (a : α) (l : Array α) : l.erase a = l.eraseP (· == a) := by
  rcases l with ⟨l⟩
  simp [List.erase_eq_eraseP']

theorem erase_eq_eraseP [LawfulBEq α] (a : α) (l : Array α) : l.erase a = l.eraseP (a == ·) := by
  rcases l with ⟨l⟩
  simp [List.erase_eq_eraseP]

@[simp] theorem erase_eq_empty_iff [LawfulBEq α] {xs : Array α} {a : α} :
    xs.erase a = #[] ↔ xs = #[] ∨ xs = #[a] := by
  rcases xs with ⟨xs⟩
  simp [List.erase_eq_nil_iff]

theorem erase_ne_empty_iff [LawfulBEq α] {xs : Array α} {a : α} :
    xs.erase a ≠ #[] ↔ xs ≠ #[] ∧ xs ≠ #[a] := by
  rcases xs with ⟨xs⟩
  simp [List.erase_ne_nil_iff]

theorem exists_erase_eq [LawfulBEq α] {a : α} {l : Array α} (h : a ∈ l) :
    ∃ l₁ l₂, a ∉ l₁ ∧ l = l₁.push a ++ l₂ ∧ l.erase a = l₁ ++ l₂ := by
  let ⟨_, l₁, l₂, h₁, e, h₂, h₃⟩ := exists_of_eraseP h (beq_self_eq_true _)
  rw [erase_eq_eraseP]; exact ⟨l₁, l₂, fun h => h₁ _ h (beq_self_eq_true _), eq_of_beq e ▸ h₂, h₃⟩

@[simp] theorem size_erase_of_mem [LawfulBEq α] {a : α} {l : Array α} (h : a ∈ l) :
    (l.erase a).size = l.size - 1 := by
  rw [erase_eq_eraseP]; exact size_eraseP_of_mem h (beq_self_eq_true a)

theorem size_erase [LawfulBEq α] (a : α) (l : Array α) :
    (l.erase a).size = if a ∈ l then l.size - 1 else l.size := by
  rw [erase_eq_eraseP, size_eraseP]
  congr
  simp [mem_iff_getElem, eq_comm (a := a)]

theorem size_erase_le (a : α) (l : Array α) : (l.erase a).size ≤ l.size := by
  rcases l with ⟨l⟩
  simpa using List.length_erase_le a l

theorem le_size_erase [LawfulBEq α] (a : α) (l : Array α) : l.size - 1 ≤ (l.erase a).size := by
  rcases l with ⟨l⟩
  simpa using List.le_length_erase a l

theorem mem_of_mem_erase {a b : α} {l : Array α} (h : a ∈ l.erase b) : a ∈ l := by
  rcases l with ⟨l⟩
  simpa using List.mem_of_mem_erase (by simpa using h)

@[simp] theorem mem_erase_of_ne [LawfulBEq α] {a b : α} {l : Array α} (ab : a ≠ b) :
    a ∈ l.erase b ↔ a ∈ l :=
  erase_eq_eraseP b l ▸ mem_eraseP_of_neg (mt eq_of_beq ab.symm)

@[simp] theorem erase_eq_self_iff [LawfulBEq α] {l : Array α} : l.erase a = l ↔ a ∉ l := by
  rw [erase_eq_eraseP', eraseP_eq_self_iff]
  simp [forall_mem_ne']

theorem erase_filter [LawfulBEq α] (f : α → Bool) (l : Array α) :
    (filter f l).erase a = filter f (l.erase a) := by
  rcases l with ⟨l⟩
  simpa using List.erase_filter f l

theorem erase_append_left [LawfulBEq α] {l₁ : Array α} (l₂) (h : a ∈ l₁) :
    (l₁ ++ l₂).erase a = l₁.erase a ++ l₂ := by
  rcases l₁ with ⟨l₁⟩
  rcases l₂ with ⟨l₂⟩
  simpa using List.erase_append_left l₂ (by simpa using h)

theorem erase_append_right [LawfulBEq α] {a : α} {l₁ : Array α} (l₂ : Array α) (h : a ∉ l₁) :
    (l₁ ++ l₂).erase a = (l₁ ++ l₂.erase a) := by
  rcases l₁ with ⟨l₁⟩
  rcases l₂ with ⟨l₂⟩
  simpa using List.erase_append_right l₂ (by simpa using h)

theorem erase_append [LawfulBEq α] {a : α} {l₁ l₂ : Array α} :
    (l₁ ++ l₂).erase a = if a ∈ l₁ then l₁.erase a ++ l₂ else l₁ ++ l₂.erase a := by
  rcases l₁ with ⟨l₁⟩
  rcases l₂ with ⟨l₂⟩
  simp only [List.append_toArray, List.erase_toArray, List.erase_append, mem_toArray]
  split <;> simp

theorem erase_mkArray [LawfulBEq α] (n : Nat) (a b : α) :
    (mkArray n a).erase b = if b == a then mkArray (n - 1) a else mkArray n a := by
  simp only [← List.toArray_replicate, List.erase_toArray]
  simp only [List.erase_replicate, beq_iff_eq, List.toArray_replicate]
  split <;> simp

theorem erase_comm [LawfulBEq α] (a b : α) (l : Array α) :
    (l.erase a).erase b = (l.erase b).erase a := by
  rcases l with ⟨l⟩
  simpa using List.erase_comm a b l

theorem erase_eq_iff [LawfulBEq α] {a : α} {l : Array α} :
    l.erase a = l' ↔
      (a ∉ l ∧ l = l') ∨
        ∃ l₁ l₂, a ∉ l₁ ∧ l = l₁.push a ++ l₂ ∧ l' = l₁ ++ l₂ := by
  rw [erase_eq_eraseP', eraseP_eq_iff]
  simp only [beq_iff_eq, forall_mem_ne', exists_and_left]
  constructor
  · rintro (⟨h, rfl⟩ | ⟨a', l', h, rfl, x, rfl, rfl⟩)
    · left; simp_all
    · right; refine ⟨l', h, x, by simp⟩
  · rintro (⟨h, rfl⟩ | ⟨l₁, h, x, rfl, rfl⟩)
    · left; simp_all
    · right; refine ⟨a, l₁, h, rfl, x, by simp⟩

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

theorem eraseIdx_eq_take_drop_succ (l : Array α) (i : Nat) (h) : l.eraseIdx i = l.take i ++ l.drop (i + 1) := by
  rcases l with ⟨l⟩
  simp only [List.size_toArray] at h
  simp only [List.eraseIdx_toArray, List.eraseIdx_eq_take_drop_succ, take_eq_extract,
    List.extract_toArray, List.extract_eq_drop_take, Nat.sub_zero, List.drop_zero, drop_eq_extract,
    List.size_toArray, List.append_toArray, mk.injEq, List.append_cancel_left_eq]
  rw [List.take_of_length_le]
  simp

theorem getElem?_eraseIdx (l : Array α) (i : Nat) (h : i < l.size) (j : Nat) :
    (l.eraseIdx i)[j]? = if j < i then l[j]? else l[j + 1]? := by
  rcases l with ⟨l⟩
  simp [List.getElem?_eraseIdx]

theorem getElem?_eraseIdx_of_lt (l : Array α) (i : Nat) (h : i < l.size) (j : Nat) (h' : j < i) :
    (l.eraseIdx i)[j]? = l[j]? := by
  rw [getElem?_eraseIdx]
  simp [h']

theorem getElem?_eraseIdx_of_ge (l : Array α) (i : Nat) (h : i < l.size) (j : Nat) (h' : i ≤ j) :
    (l.eraseIdx i)[j]? = l[j + 1]? := by
  rw [getElem?_eraseIdx]
  simp only [dite_eq_ite, ite_eq_right_iff]
  intro h'
  omega

theorem getElem_eraseIdx (l : Array α) (i : Nat) (h : i < l.size) (j : Nat) (h' : j < (l.eraseIdx i).size) :
    (l.eraseIdx i)[j] = if h'' : j < i then
        l[j]
      else
        l[j + 1]'(by rw [size_eraseIdx] at h'; omega) := by
  apply Option.some.inj
  rw [← getElem?_eq_getElem, getElem?_eraseIdx]
  split <;> simp

@[simp] theorem eraseIdx_eq_empty_iff {l : Array α} {i : Nat} {h} : eraseIdx l i = #[] ↔ l.size = 1 ∧ i = 0 := by
  rcases l with ⟨l⟩
  simp only [List.eraseIdx_toArray, mk.injEq, List.eraseIdx_eq_nil_iff, List.size_toArray,
    or_iff_right_iff_imp]
  rintro rfl
  simp_all

theorem eraseIdx_ne_empty_iff {l : Array α} {i : Nat} {h} : eraseIdx l i ≠ #[] ↔ 2 ≤ l.size := by
  rcases l with ⟨_ | ⟨a, (_ | ⟨b, l⟩)⟩⟩
  · simp
  · simp at h
    simp [h]
  · simp

theorem mem_of_mem_eraseIdx {l : Array α} {i : Nat} {h} {a : α} (h : a ∈ l.eraseIdx i) : a ∈ l := by
  rcases l with ⟨l⟩
  simpa using List.mem_of_mem_eraseIdx (by simpa using h)

theorem eraseIdx_append_of_lt_size {l : Array α} {k : Nat} (hk : k < l.size) (l' : Array α) (h) :
    eraseIdx (l ++ l') k = eraseIdx l k ++ l' := by
  rcases l with ⟨l⟩
  rcases l' with ⟨l'⟩
  simp at hk
  simp [List.eraseIdx_append_of_lt_length, *]

theorem eraseIdx_append_of_length_le {l : Array α} {k : Nat} (hk : l.size ≤ k) (l' : Array α) (h) :
    eraseIdx (l ++ l') k = l ++ eraseIdx l' (k - l.size) (by simp at h; omega) := by
  rcases l with ⟨l⟩
  rcases l' with ⟨l'⟩
  simp at hk
  simp [List.eraseIdx_append_of_length_le, *]

theorem eraseIdx_mkArray {n : Nat} {a : α} {k : Nat} {h} :
    (mkArray n a).eraseIdx k = mkArray (n - 1) a := by
  simp at h
  simp only [← List.toArray_replicate, List.eraseIdx_toArray]
  simp [List.eraseIdx_replicate, h]

theorem mem_eraseIdx_iff_getElem {x : α} {l} {k} {h} : x ∈ eraseIdx l k h ↔ ∃ i w, i ≠ k ∧ l[i]'w = x := by
  rcases l with ⟨l⟩
  simp [List.mem_eraseIdx_iff_getElem, *]

theorem mem_eraseIdx_iff_getElem? {x : α} {l} {k} {h} : x ∈ eraseIdx l k h ↔ ∃ i ≠ k, l[i]? = some x := by
  rcases l with ⟨l⟩
  simp [List.mem_eraseIdx_iff_getElem?, *]

theorem erase_eq_eraseIdx_of_idxOf [BEq α] [LawfulBEq α] (l : Array α) (a : α) (i : Nat) (w : l.idxOf a = i) (h : i < l.size) :
    l.erase a = l.eraseIdx i := by
  rcases l with ⟨l⟩
  simp at w
  simp [List.erase_eq_eraseIdx_of_idxOf, *]

theorem getElem_eraseIdx_of_lt (l : Array α) (i : Nat) (w : i < l.size) (j : Nat) (h : j < (l.eraseIdx i).size) (h' : j < i) :
    (l.eraseIdx i)[j] = l[j] := by
  rcases l with ⟨l⟩
  simp [List.getElem_eraseIdx_of_lt, *]

theorem getElem_eraseIdx_of_ge (l : Array α) (i : Nat) (w : i < l.size) (j : Nat) (h : j < (l.eraseIdx i).size) (h' : i ≤ j) :
    (l.eraseIdx i)[j] = l[j + 1]'(by simp at h; omega) := by
  rcases l with ⟨l⟩
  simp [List.getElem_eraseIdx_of_ge, *]

theorem eraseIdx_set_eq {l : Array α} {i : Nat} {a : α} {h : i < l.size} :
    (l.set i a).eraseIdx i (by simp; omega) = l.eraseIdx i := by
  rcases l with ⟨l⟩
  simp [List.eraseIdx_set_eq, *]

theorem eraseIdx_set_lt {l : Array α} {i : Nat} {w : i < l.size} {j : Nat} {a : α} (h : j < i) :
    (l.set i a).eraseIdx j (by simp; omega) = (l.eraseIdx j).set (i - 1) a (by simp; omega) := by
  rcases l with ⟨l⟩
  simp [List.eraseIdx_set_lt, *]

theorem eraseIdx_set_gt {l : Array α} {i : Nat} {j : Nat} {a : α} (h : i < j) {w : j < l.size} :
    (l.set i a).eraseIdx j (by simp; omega) = (l.eraseIdx j).set i a (by simp; omega) := by
  rcases l with ⟨l⟩
  simp [List.eraseIdx_set_gt, *]

@[simp] theorem set_getElem_succ_eraseIdx_succ
    {l : Array α} {i : Nat} (h : i + 1 < l.size) :
    (l.eraseIdx (i + 1)).set i l[i + 1] (by simp; omega) = l.eraseIdx i := by
  rcases l with ⟨l⟩
  simp [List.set_getElem_succ_eraseIdx_succ, *]

end Array
