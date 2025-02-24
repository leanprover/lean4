/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
prelude
import Init.Data.List.Nat.Modify

/-!
# insertIdx

Proves various lemmas about `List.insertIdx`.
-/

-- set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
-- set_option linter.indexVariables true -- Enforce naming conventions for index variables.

open Function Nat

namespace List

universe u

variable {α : Type u}

section InsertIdx

variable {a : α}

@[simp]
theorem insertIdx_zero (s : List α) (x : α) : insertIdx 0 x s = x :: s :=
  rfl

@[simp]
theorem insertIdx_succ_nil (n : Nat) (a : α) : insertIdx (n + 1) a [] = [] :=
  rfl

@[simp]
theorem insertIdx_succ_cons (s : List α) (hd x : α) (i : Nat) :
    insertIdx (i + 1) x (hd :: s) = hd :: insertIdx i x s :=
  rfl

theorem length_insertIdx : ∀ i as, (insertIdx i a as).length = if i ≤ as.length then as.length + 1 else as.length
  | 0, _ => by simp
  | n + 1, [] => by simp
  | n + 1, a :: as => by
    simp only [insertIdx_succ_cons, length_cons, length_insertIdx, Nat.add_le_add_iff_right]
    split <;> rfl

theorem length_insertIdx_of_le_length (h : i ≤ length as) : length (insertIdx i a as) = length as + 1 := by
  simp [length_insertIdx, h]

theorem length_insertIdx_of_length_lt (h : length as < i) : length (insertIdx i a as) = length as := by
  simp [length_insertIdx, h]

@[simp]
theorem eraseIdx_insertIdx (i : Nat) (l : List α) : (l.insertIdx i a).eraseIdx i = l := by
  rw [eraseIdx_eq_modifyTailIdx, insertIdx, modifyTailIdx_modifyTailIdx_self]
  exact modifyTailIdx_id _ _

theorem insertIdx_eraseIdx_of_ge :
    ∀ i m as,
      i < length as → i ≤ m → insertIdx m a (as.eraseIdx i) = (as.insertIdx (m + 1) a).eraseIdx i
  | 0, 0, [], has, _ => (Nat.lt_irrefl _ has).elim
  | 0, 0, _ :: as, _, _ => by simp [eraseIdx, insertIdx]
  | 0, _ + 1, _ :: _, _, _ => rfl
  | n + 1, m + 1, a :: as, has, hmn =>
    congrArg (cons a) <|
      insertIdx_eraseIdx_of_ge n m as (Nat.lt_of_succ_lt_succ has) (Nat.le_of_succ_le_succ hmn)

theorem insertIdx_eraseIdx_of_le :
    ∀ i j as,
      i < length as → j ≤ i → insertIdx j a (as.eraseIdx i) = (as.insertIdx j a).eraseIdx (i + 1)
  | _, 0, _ :: _, _, _ => rfl
  | n + 1, m + 1, a :: as, has, hmn =>
    congrArg (cons a) <|
      insertIdx_eraseIdx_of_le n m as (Nat.lt_of_succ_lt_succ has) (Nat.le_of_succ_le_succ hmn)

theorem insertIdx_comm (a b : α) :
    ∀ (i j : Nat) (l : List α) (_ : i ≤ j) (_ : j ≤ length l),
      (l.insertIdx i a).insertIdx (j + 1) b = (l.insertIdx j b).insertIdx i a
  | 0, j, l => by simp [insertIdx]
  | _ + 1, 0, _ => fun h => (Nat.not_lt_zero _ h).elim
  | i + 1, j + 1, [] => by simp
  | i + 1, j + 1, c :: l => fun h₀ h₁ => by
    simp only [insertIdx_succ_cons, cons.injEq, true_and]
    exact insertIdx_comm a b i j l (Nat.le_of_succ_le_succ h₀) (Nat.le_of_succ_le_succ h₁)

theorem mem_insertIdx {a b : α} :
    ∀ {i : Nat} {l : List α} (_ : i ≤ l.length), a ∈ l.insertIdx i b ↔ a = b ∨ a ∈ l
  | 0, as, _ => by simp
  | _ + 1, [], h => (Nat.not_succ_le_zero _ h).elim
  | n + 1, a' :: as, h => by
    rw [List.insertIdx_succ_cons, mem_cons, mem_insertIdx (Nat.le_of_succ_le_succ h),
      ← or_assoc, @or_comm (a = a'), or_assoc, mem_cons]

theorem insertIdx_of_length_lt (l : List α) (x : α) (i : Nat) (h : l.length < i) :
    insertIdx i x l = l := by
  induction l generalizing i with
  | nil =>
    cases i
    · simp at h
    · simp
  | cons x l ih =>
    cases i
    · simp at h
    · simp only [Nat.succ_lt_succ_iff, length] at h
      simpa using ih _ h

@[simp]
theorem insertIdx_length_self (l : List α) (x : α) : insertIdx l.length x l = l ++ [x] := by
  induction l with
  | nil => simp
  | cons x l ih => simpa using ih

theorem length_le_length_insertIdx (l : List α) (x : α) (i : Nat) :
    l.length ≤ (insertIdx i x l).length := by
  simp only [length_insertIdx]
  split <;> simp

theorem length_insertIdx_le_succ (l : List α) (x : α) (i : Nat) :
    (insertIdx i x l).length ≤ l.length + 1 := by
  simp only [length_insertIdx]
  split <;> simp

theorem getElem_insertIdx_of_lt {l : List α} {x : α} {i j : Nat} (hn : j < i)
    (hk : j < (insertIdx i x l).length) :
    (insertIdx i x l)[j] = l[j]'(by simp [length_insertIdx] at hk; split at hk <;> omega) := by
  induction i generalizing j l with
  | zero => simp at hn
  | succ n ih =>
    cases l with
    | nil => simp
    | cons _ _=>
      cases j
      · simp
      · rw [Nat.succ_lt_succ_iff] at hn
        simpa using ih hn _

@[simp]
theorem getElem_insertIdx_self {l : List α} {x : α} {i : Nat} (hi : i < (insertIdx i x l).length) :
    (insertIdx i x l)[i] = x := by
  induction l generalizing i with
  | nil =>
    simp [length_insertIdx] at hi
    split at hi
    · simp_all
    · omega
  | cons _ _ ih =>
    cases i
    · simp
    · simp only [insertIdx_succ_cons, length_cons, length_insertIdx, Nat.add_lt_add_iff_right] at hi ih
      simpa using ih hi

theorem getElem_insertIdx_of_gt {l : List α} {x : α} {i j : Nat} (hn : i < j)
    (hk : j < (insertIdx i x l).length) :
    (insertIdx i x l)[j] = l[j - 1]'(by simp [length_insertIdx] at hk; split at hk <;> omega) := by
  induction l generalizing i j with
  | nil =>
    cases i with
    | zero =>
      simp only [insertIdx_zero, length_singleton, lt_one_iff] at hk
      omega
    | succ n => simp at hk
  | cons _ _ ih =>
    cases i with
    | zero =>
      simp only [insertIdx_zero] at hk
      cases j with
      | zero => omega
      | succ j => simp
    | succ n =>
      cases j with
      | zero => simp
      | succ j =>
        simp only [insertIdx_succ_cons, getElem_cons_succ]
        rw [ih (by omega)]
        cases j with
        | zero => omega
        | succ j => simp

@[deprecated getElem_insertIdx_of_gt (since := "2025-02-04")]
abbrev getElem_insertIdx_of_ge := @getElem_insertIdx_of_gt

theorem getElem_insertIdx {l : List α} {x : α} {i j : Nat} (h : j < (insertIdx i x l).length) :
    (insertIdx i x l)[j] =
      if h₁ : j < i then
        l[j]'(by simp [length_insertIdx] at h; split at h <;> omega)
      else
        if h₂ : j = i then
          x
        else
          l[j-1]'(by simp [length_insertIdx] at h; split at h <;> omega) := by
  split <;> rename_i h₁
  · rw [getElem_insertIdx_of_lt h₁]
  · split <;> rename_i h₂
    · subst h₂
      rw [getElem_insertIdx_self h]
    · rw [getElem_insertIdx_of_gt (by omega)]

theorem getElem?_insertIdx {l : List α} {x : α} {i j : Nat} :
    (insertIdx i x l)[j]? =
      if j < i then
        l[j]?
      else
        if j = i then
          if j ≤ l.length then some x else none
        else
          l[j-1]? := by
  rw [getElem?_def]
  split <;> rename_i h
  · rw [getElem_insertIdx h]
    simp only [length_insertIdx] at h
    split <;> rename_i h₁
    · rw [getElem?_def, dif_pos]
    · split <;> rename_i h₂
      · rw [if_pos]
        split at h <;> omega
      · rw [getElem?_def]
        simp only [Option.some_eq_dite_none_right, exists_prop, and_true]
        split at h <;> omega
  · simp only [length_insertIdx] at h
    split <;> rename_i h₁
    · rw [getElem?_eq_none]
      split at h <;> omega
    · split <;> rename_i h₂
      · rw [if_neg]
        split at h <;> omega
      · rw [getElem?_eq_none]
        split at h <;> omega

theorem getElem?_insertIdx_of_lt {l : List α} {x : α} {i j : Nat} (h : j < i) :
    (insertIdx i x l)[j]? = l[j]? := by
  rw [getElem?_insertIdx, if_pos h]

theorem getElem?_insertIdx_self {l : List α} {x : α} {i : Nat} :
    (insertIdx i x l)[i]? = if i ≤ l.length then some x else none := by
  rw [getElem?_insertIdx, if_neg (by omega)]
  simp

theorem getElem?_insertIdx_of_gt {l : List α} {x : α} {i j : Nat} (h : i < j) :
    (insertIdx i x l)[j]? = l[j - 1]? := by
  rw [getElem?_insertIdx, if_neg (by omega), if_neg (by omega)]

@[deprecated getElem?_insertIdx_of_gt (since := "2025-02-04")]
abbrev getElem?_insertIdx_of_ge := @getElem?_insertIdx_of_gt

end InsertIdx

end List
