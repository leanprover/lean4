/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
module

prelude
public import Init.GetElem
import Init.Data.List.Erase
import Init.Data.List.Lemmas
import Init.Data.List.Nat.Modify
import Init.Data.Nat.Lemmas
import Init.Data.Option.Lemmas
import Init.Omega

public section

/-!
# insertIdx

Proves various lemmas about `List.insertIdx`.
-/

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

open Function Nat

namespace List

universe u

variable {α : Type u}

section InsertIdx

variable {a : α}

@[simp, grind =]
theorem insertIdx_zero {xs : List α} {x : α} : xs.insertIdx 0 x = x :: xs :=
  rfl

@[simp, grind =]
theorem insertIdx_succ_nil {n : Nat} {a : α} : ([] : List α).insertIdx (n + 1) a = [] :=
  rfl

@[simp, grind =]
theorem insertIdx_succ_cons {xs : List α} {hd x : α} {i : Nat} :
    (hd :: xs).insertIdx (i + 1) x = hd :: xs.insertIdx i x :=
  rfl

@[grind =]
theorem length_insertIdx : ∀ {i} {as : List α}, (as.insertIdx i a).length = if i ≤ as.length then as.length + 1 else as.length
  | 0, _ => by simp
  | n + 1, [] => by simp
  | n + 1, a :: as => by
    simp only [insertIdx_succ_cons, length_cons, length_insertIdx, Nat.add_le_add_iff_right]
    split <;> rfl

theorem length_insertIdx_of_le_length (h : i ≤ length as) (a : α) : (as.insertIdx i a).length = as.length + 1 := by
  simp [length_insertIdx, h]

theorem length_insertIdx_of_length_lt (h : length as < i) (a : α) : (as.insertIdx i a).length = as.length := by
  simp [length_insertIdx, h]

theorem insertIdx_eraseIdx_of_ge :
    ∀ {i j as},
      i < length as → i ≤ j → (as.eraseIdx i).insertIdx j a = (as.insertIdx (j + 1) a).eraseIdx i
  | 0, 0, [], has, _ => (Nat.lt_irrefl _ has).elim
  | 0, 0, _ :: as, _, _ => by simp [eraseIdx, insertIdx]
  | 0, _ + 1, _ :: _, _, _ => rfl
  | n + 1, m + 1, a :: as, has, hmn =>
    congrArg (cons a) <|
      insertIdx_eraseIdx_of_ge (Nat.lt_of_succ_lt_succ has) (Nat.le_of_succ_le_succ hmn)

theorem insertIdx_eraseIdx_of_le :
    ∀ {i j as},
      i < length as → j ≤ i → (as.eraseIdx i).insertIdx j a = (as.insertIdx j a).eraseIdx (i + 1)
  | _, 0, _ :: _, _, _ => rfl
  | _ + 1, _ + 1, a :: _, has, hmn =>
    congrArg (cons a) <|
      insertIdx_eraseIdx_of_le (Nat.lt_of_succ_lt_succ has) (Nat.le_of_succ_le_succ hmn)

@[grind =]
theorem insertIdx_eraseIdx (h : i < length as) :
    (as.eraseIdx i).insertIdx j a =
      if i ≤ j then (as.insertIdx (j + 1) a).eraseIdx i else (as.insertIdx j a).eraseIdx (i + 1) := by
  split <;> rename_i h'
  · rw [insertIdx_eraseIdx_of_ge h h']
  · rw [insertIdx_eraseIdx_of_le h (by omega)]

@[grind =]
theorem insertIdx_comm (a b : α) :
    ∀ {i j : Nat} {l : List α} (_ : i ≤ j) (_ : j ≤ length l),
      (l.insertIdx i a).insertIdx (j + 1) b = (l.insertIdx j b).insertIdx i a
  | 0, j, l => by simp [insertIdx]
  | _ + 1, 0, _ => fun h => (Nat.not_lt_zero _ h).elim
  | i + 1, j + 1, [] => by simp
  | i + 1, j + 1, c :: l => fun h₀ h₁ => by
    simp only [insertIdx_succ_cons, cons.injEq, true_and]
    exact insertIdx_comm a b (Nat.le_of_succ_le_succ h₀) (Nat.le_of_succ_le_succ h₁)

theorem mem_insertIdx {a b : α} :
    ∀ {i : Nat} {l : List α} (_ : i ≤ l.length), a ∈ l.insertIdx i b ↔ a = b ∨ a ∈ l
  | 0, as, _ => by simp
  | _ + 1, [], h => (Nat.not_succ_le_zero _ h).elim
  | n + 1, a' :: as, h => by
    rw [List.insertIdx_succ_cons, mem_cons, mem_insertIdx (Nat.le_of_succ_le_succ h),
      ← or_assoc, @or_comm (a = a'), or_assoc, mem_cons]

theorem insertIdx_of_length_lt {l : List α} {x : α} {i : Nat} (h : l.length < i) :
    l.insertIdx i x = l := by
  induction l generalizing i with
  | nil =>
    cases i
    · simp at h
    · simp
  | cons x l ih =>
    cases i
    · simp at h
    · simp only [Nat.succ_lt_succ_iff, length] at h
      simpa using ih h

@[simp, grind =]
theorem eraseIdx_insertIdx_self {i : Nat} {l : List α} (a : α) : (l.insertIdx i a).eraseIdx i = l := by
  rw [eraseIdx_eq_modifyTailIdx, insertIdx, modifyTailIdx_modifyTailIdx_self]
  exact modifyTailIdx_id _ _

@[simp]
theorem insertIdx_length_self {l : List α} {x : α} : l.insertIdx l.length x = l ++ [x] := by
  induction l with
  | nil => simp
  | cons x l ih => simpa using ih

theorem length_le_length_insertIdx {l : List α} {x : α} {i : Nat} :
    l.length ≤ (l.insertIdx i x).length := by
  simp only [length_insertIdx]
  split <;> simp

theorem length_insertIdx_le_succ {l : List α} {x : α} {i : Nat} :
    (l.insertIdx i x).length ≤ l.length + 1 := by
  simp only [length_insertIdx]
  split <;> simp

theorem getElemV_insertIdx_of_lt {l : List α} {a : α} {i j : Nat} (h : j < i) :
    haveI : Nonempty α := ⟨a⟩
    (l.insertIdx i a)｢j｣ = l｢j｣ := by
  induction i generalizing j l with
  | zero => simp at h
  | succ n ih =>
    cases l with
    | nil => simp
    | cons _ _=>
      cases j
      · simp
      · rw [Nat.succ_lt_succ_iff] at h
        simpa [getElemV_cons_succ ] using ih h

theorem getElem_insertIdx_of_lt {l : List α} {x : α} {i j : Nat} (hn : j < i)
    (hk : j < (l.insertIdx i x).length) :
    (l.insertIdx i x)[j]'hk = l[j]'(by simp [length_insertIdx] at hk; split at hk <;> omega) := by
  simp [getElemV_insertIdx_of_lt hn]

@[simp]
theorem getElemV_insertIdx_self {l : List α} {a : α} {i : Nat} (w : i ≤ l.length) :
    haveI : Nonempty α := ⟨a⟩
    (l.insertIdx i a)｢i｣ = a := by
  induction l generalizing i with
  | nil =>
    simp only [length_nil, le_zero_eq] at w
    simp [w]
  | cons _ _ ih =>
    cases i
    · simp
    · rw [insertIdx_succ_cons, getElemV_cons_succ, ih]
      simpa using w

@[simp]
theorem getElem_insertIdx_self {l : List α} {x : α} {i : Nat} (hi : i < (l.insertIdx i x).length) :
    (l.insertIdx i x)[i] = x := by
  have : i ≤ l.length := Nat.le_of_lt_add_one (Nat.lt_of_lt_of_le hi length_insertIdx_le_succ)
  simp [getElemV_insertIdx_self this]

theorem getElemV_insertIdx_of_gt {l : List α} {a : α} {i j : Nat} (h : i < j) :
    haveI : Nonempty α := ⟨a⟩
    (l.insertIdx i a)｢j｣ = l｢j - 1｣ := by
  induction l generalizing i j with
  | nil =>
    cases i with
    | zero =>
      match j with | j' + 1 => simp
    | succ n => simp [getElemV_neg]
  | cons _ _ ih =>
    cases i with
    | zero =>
      simp only [insertIdx_zero]
      cases j with
      | zero => omega
      | succ j => simp
    | succ n =>
      cases j with
      | zero => simp
      | succ j =>
        simp only [insertIdx_succ_cons, getElemV_cons_succ]
        rw [ih (by omega)]
        cases j with
        | zero => omega
        | succ j => simp

theorem getElem_insertIdx_of_gt {l : List α} {x : α} {i j : Nat} (hn : i < j)
    (hk : j < (l.insertIdx i x).length) :
    (l.insertIdx i x)[j] = l[j - 1]'(by simp [length_insertIdx] at hk; split at hk <;> omega) := by
  simp [getElemV_insertIdx_of_gt hn]

@[grind =]
theorem getElemV_insertIdx {l : List α} {a : α} {i j : Nat} (h : j ≤ l.length) :
    haveI : Nonempty α := ⟨a⟩
    (l.insertIdx i a)｢j｣ = if j < i then l｢j｣ else if j = i then a else l｢j - 1｣ := by
  split <;> rename_i h₁
  · rw [getElemV_insertIdx_of_lt h₁]
  · split <;> rename_i h₂
    · subst h₂
      rw [getElemV_insertIdx_self h]
    · rw [getElemV_insertIdx_of_gt (by omega)]

/-
PLOG(getElem_insertIdx):
had to manually prove a weaker bound
had to use `ite_eq_dite` because of spurious dependencies
-/

theorem getElem_insertIdx {l : List α} {x : α} {i j : Nat} (h : j < (l.insertIdx i x).length) :
    (l.insertIdx i x)[j] =
      if h₁ : j < i then
        l[j]'(by simp [length_insertIdx] at h; split at h <;> omega)
      else
        if h₂ : j = i then
          x
        else
          l[j-1]'(by simp [length_insertIdx] at h; split at h <;> omega) := by
  simp only [getElem_eq_getElemV]
  have : j ≤ l.length := Nat.le_of_lt_add_one (Nat.lt_of_lt_of_le h length_insertIdx_le_succ)
  rw [getElemV_insertIdx (by omega), ite_eq_dite, ite_eq_dite]

@[grind =]
theorem getElem?_insertIdx {l : List α} {x : α} {i j : Nat} :
    (l.insertIdx i x)[j]? =
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
    (l.insertIdx i x)[j]? = l[j]? := by
  rw [getElem?_insertIdx, if_pos h]

theorem getElem?_insertIdx_self {l : List α} {x : α} {i : Nat} :
    (l.insertIdx i x)[i]? = if i ≤ l.length then some x else none := by
  rw [getElem?_insertIdx, if_neg (by omega)]
  simp

theorem getElem?_insertIdx_of_gt {l : List α} {x : α} {i j : Nat} (h : i < j) :
    (l.insertIdx i x)[j]? = l[j - 1]? := by
  rw [getElem?_insertIdx, if_neg (by omega), if_neg (by omega)]

end InsertIdx

end List
