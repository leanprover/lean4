/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Array.Basic
import Init.Data.BEq
import Init.Data.List.Nat.BEq
import Init.ByCases

-- set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
-- set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace Array

private theorem rel_of_isEqvAux
    {r : α → α → Bool} {xs ys : Array α} (hsz : xs.size = ys.size) {i : Nat} (hi : i ≤ xs.size)
    (heqv : Array.isEqvAux xs ys hsz r i hi)
    {j : Nat} (hj : j < i) : r (xs[j]'(Nat.lt_of_lt_of_le hj hi)) (ys[j]'(Nat.lt_of_lt_of_le hj (hsz ▸ hi))) := by
  induction i with
  | zero => contradiction
  | succ i ih =>
    simp only [Array.isEqvAux, Bool.and_eq_true, decide_eq_true_eq] at heqv
    by_cases hj' : j < i
    next =>
      exact ih _ heqv.right hj'
    next =>
      replace hj' : j = i := Nat.eq_of_le_of_lt_succ (Nat.not_lt.mp hj') hj
      subst hj'
      exact heqv.left

private theorem isEqvAux_of_rel {r : α → α → Bool} {xs ys : Array α} (hsz : xs.size = ys.size) {i : Nat} (hi : i ≤ xs.size)
    (w : ∀ j, (hj : j < i) → r (xs[j]'(Nat.lt_of_lt_of_le hj hi)) (ys[j]'(Nat.lt_of_lt_of_le hj (hsz ▸ hi)))) : Array.isEqvAux xs ys hsz r i hi := by
  induction i with
  | zero => simp [Array.isEqvAux]
  | succ i ih =>
    simp only [isEqvAux, Bool.and_eq_true]
    exact ⟨w i (Nat.lt_add_one i), ih _ fun j hj => w j (Nat.lt_add_right 1 hj)⟩

-- This is private as the forward direction of `isEqv_iff_rel` may be used.
private theorem rel_of_isEqv {r : α → α → Bool} {xs ys : Array α} :
    Array.isEqv xs ys r → ∃ h : xs.size = ys.size, ∀ (i : Nat) (h' : i < xs.size), r (xs[i]) (ys[i]'(h ▸ h')) := by
  simp only [isEqv]
  split <;> rename_i h
  · exact fun h' => ⟨h, fun i => rel_of_isEqvAux h (Nat.le_refl ..) h'⟩
  · intro; contradiction

theorem isEqv_iff_rel {xs ys : Array α} {r} :
    Array.isEqv xs ys r ↔ ∃ h : xs.size = ys.size, ∀ (i : Nat) (h' : i < xs.size), r (xs[i]) (ys[i]'(h ▸ h')) :=
  ⟨rel_of_isEqv, fun ⟨h, w⟩ => by
    simp only [isEqv, ← h, ↓reduceDIte]
    exact isEqvAux_of_rel h (by simp [h]) w⟩

theorem isEqv_eq_decide (xs ys : Array α) (r) :
    Array.isEqv xs ys r =
      if h : xs.size = ys.size then decide (∀ (i : Nat) (h' : i < xs.size), r (xs[i]) (ys[i]'(h ▸ h'))) else false := by
  by_cases h : Array.isEqv xs ys r
  · simp only [h, Bool.true_eq]
    simp only [isEqv_iff_rel] at h
    obtain ⟨h, w⟩ := h
    simp [h, w]
  · let h' := h
    simp only [Bool.not_eq_true] at h
    simp only [h, Bool.false_eq, dite_eq_right_iff, decide_eq_false_iff_not, Classical.not_forall,
      Bool.not_eq_true]
    simpa [isEqv_iff_rel] using h'

@[simp] theorem isEqv_toList [BEq α] (xs ys : Array α) : (xs.toList.isEqv ys.toList r) = (xs.isEqv ys r) := by
  simp [isEqv_eq_decide, List.isEqv_eq_decide]

theorem eq_of_isEqv [DecidableEq α] (xs ys : Array α) (h : Array.isEqv xs ys (fun x y => x = y)) : xs = ys := by
  have ⟨h, h'⟩ := rel_of_isEqv h
  exact ext _ _ h (fun i lt _ => by simpa using h' i lt)

private theorem isEqvAux_self (r : α → α → Bool) (hr : ∀ a, r a a) (xs : Array α) (i : Nat) (h : i ≤ xs.size) :
    Array.isEqvAux xs xs rfl r i h = true := by
  induction i with
  | zero => simp [Array.isEqvAux]
  | succ i ih =>
    simp_all only [isEqvAux, Bool.and_self]

theorem isEqv_self_beq [BEq α] [ReflBEq α] (xs : Array α) : Array.isEqv xs xs (· == ·) = true := by
  simp [isEqv, isEqvAux_self]

theorem isEqv_self [DecidableEq α] (xs : Array α) : Array.isEqv xs xs (· = ·) = true := by
  simp [isEqv, isEqvAux_self]

instance [DecidableEq α] : DecidableEq (Array α) :=
  fun xs ys =>
    match h:isEqv xs ys (fun a b => a = b) with
    | true  => isTrue (eq_of_isEqv xs ys h)
    | false => isFalse fun h' => by subst h'; rw [isEqv_self] at h; contradiction

theorem beq_eq_decide [BEq α] (xs ys : Array α) :
    (xs == ys) = if h : xs.size = ys.size then
      decide (∀ (i : Nat) (h' : i < xs.size), xs[i] == ys[i]'(h ▸ h')) else false := by
  simp [BEq.beq, isEqv_eq_decide]

@[simp] theorem beq_toList [BEq α] (xs ys : Array α) : (xs.toList == ys.toList) = (xs == ys) := by
  simp [beq_eq_decide, List.beq_eq_decide]

end Array

namespace List

@[simp] theorem isEqv_toArray [BEq α] (as bs : List α) : (as.toArray.isEqv bs.toArray r) = (as.isEqv bs r) := by
  simp [isEqv_eq_decide, Array.isEqv_eq_decide]

@[simp] theorem beq_toArray [BEq α] (as bs : List α) : (as.toArray == bs.toArray) = (as == bs) := by
  simp [beq_eq_decide, Array.beq_eq_decide]

end List

namespace Array

instance [BEq α] [LawfulBEq α] : LawfulBEq (Array α) where
  rfl := by simp [BEq.beq, isEqv_self_beq]
  eq_of_beq := by
    rintro ⟨_⟩ ⟨_⟩ h
    simpa using h

end Array
