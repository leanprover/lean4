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

namespace Array

theorem rel_of_isEqvAux
    {r : α → α → Bool} {a b : Array α} (hsz : a.size = b.size) {i : Nat} (hi : i ≤ a.size)
    (heqv : Array.isEqvAux a b hsz r i hi)
    {j : Nat} (hj : j < i) : r (a[j]'(Nat.lt_of_lt_of_le hj hi)) (b[j]'(Nat.lt_of_lt_of_le hj (hsz ▸ hi))) := by
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

theorem isEqvAux_of_rel {r : α → α → Bool} {a b : Array α} (hsz : a.size = b.size) {i : Nat} (hi : i ≤ a.size)
    (w : ∀ j, (hj : j < i) → r (a[j]'(Nat.lt_of_lt_of_le hj hi)) (b[j]'(Nat.lt_of_lt_of_le hj (hsz ▸ hi)))) : Array.isEqvAux a b hsz r i hi := by
  induction i with
  | zero => simp [Array.isEqvAux]
  | succ i ih =>
    simp only [isEqvAux, Bool.and_eq_true]
    exact ⟨w i (Nat.lt_add_one i), ih _ fun j hj => w j (Nat.lt_add_right 1 hj)⟩

theorem rel_of_isEqv {r : α → α → Bool} {a b : Array α} :
    Array.isEqv a b r → ∃ h : a.size = b.size, ∀ (i : Nat) (h' : i < a.size), r (a[i]) (b[i]'(h ▸ h')) := by
  simp only [isEqv]
  split <;> rename_i h
  · exact fun h' => ⟨h, fun i => rel_of_isEqvAux h (Nat.le_refl ..) h'⟩
  · intro; contradiction

theorem isEqv_iff_rel (a b : Array α) (r) :
    Array.isEqv a b r ↔ ∃ h : a.size = b.size, ∀ (i : Nat) (h' : i < a.size), r (a[i]) (b[i]'(h ▸ h')) :=
  ⟨rel_of_isEqv, fun ⟨h, w⟩ => by
    simp only [isEqv, ← h, ↓reduceDIte]
    exact isEqvAux_of_rel h (by simp [h]) w⟩

theorem isEqv_eq_decide (a b : Array α) (r) :
    Array.isEqv a b r =
      if h : a.size = b.size then decide (∀ (i : Nat) (h' : i < a.size), r (a[i]) (b[i]'(h ▸ h'))) else false := by
  by_cases h : Array.isEqv a b r
  · simp only [h, Bool.true_eq]
    simp only [isEqv_iff_rel] at h
    obtain ⟨h, w⟩ := h
    simp [h, w]
  · let h' := h
    simp only [Bool.not_eq_true] at h
    simp only [h, Bool.false_eq, dite_eq_right_iff, decide_eq_false_iff_not, Classical.not_forall,
      Bool.not_eq_true]
    simpa [isEqv_iff_rel] using h'

@[simp] theorem isEqv_toList [BEq α] (a b : Array α) : (a.toList.isEqv b.toList r) = (a.isEqv b r) := by
  simp [isEqv_eq_decide, List.isEqv_eq_decide]

theorem eq_of_isEqv [DecidableEq α] (a b : Array α) (h : Array.isEqv a b (fun x y => x = y)) : a = b := by
  have ⟨h, h'⟩ := rel_of_isEqv h
  exact ext _ _ h (fun i lt _ => by simpa using h' i lt)

theorem isEqvAux_self (r : α → α → Bool) (hr : ∀ a, r a a) (a : Array α) (i : Nat) (h : i ≤ a.size) :
    Array.isEqvAux a a rfl r i h = true := by
  induction i with
  | zero => simp [Array.isEqvAux]
  | succ i ih =>
    simp_all only [isEqvAux, Bool.and_self]

theorem isEqv_self_beq [BEq α] [ReflBEq α] (a : Array α) : Array.isEqv a a (· == ·) = true := by
  simp [isEqv, isEqvAux_self]

theorem isEqv_self [DecidableEq α] (a : Array α) : Array.isEqv a a (· = ·) = true := by
  simp [isEqv, isEqvAux_self]

instance [DecidableEq α] : DecidableEq (Array α) :=
  fun a b =>
    match h:isEqv a b (fun a b => a = b) with
    | true  => isTrue (eq_of_isEqv a b h)
    | false => isFalse fun h' => by subst h'; rw [isEqv_self] at h; contradiction

theorem beq_eq_decide [BEq α] (a b : Array α) :
    (a == b) = if h : a.size = b.size then
      decide (∀ (i : Nat) (h' : i < a.size), a[i] == b[i]'(h ▸ h')) else false := by
  simp [BEq.beq, isEqv_eq_decide]

@[simp] theorem beq_toList [BEq α] (a b : Array α) : (a.toList == b.toList) = (a == b) := by
  simp [beq_eq_decide, List.beq_eq_decide]

end Array

namespace List

@[simp] theorem isEqv_toArray [BEq α] (a b : List α) : (a.toArray.isEqv b.toArray r) = (a.isEqv b r) := by
  simp [isEqv_eq_decide, Array.isEqv_eq_decide]

@[simp] theorem beq_toArray [BEq α] (a b : List α) : (a.toArray == b.toArray) = (a == b) := by
  simp [beq_eq_decide, Array.beq_eq_decide]

end List
