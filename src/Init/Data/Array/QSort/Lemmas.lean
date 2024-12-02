/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Array.QSort.Basic
import Init.Data.Vector.Lemmas
import Init.Data.Array.Perm

namespace Array

open List Vector

@[simp] theorem size_qsort (as : Array α) (lt : α → α → Bool) (lo hi : Nat) :
    (qsort as lt lo hi).size = as.size := by
  unfold qsort
  split
  · rfl
  · simp

theorem qpartition_loop_perm {n} (as : Vector α n) (lt : α → α → Bool) (lo hi : Nat)
    {hhi} {ilo} {jh} :
    (qpartition.loop lt lo hi hhi pivot as i j ilo jh w).2.toArray ~ as.toArray := by
  unfold qpartition.loop
  split
  · split
    · exact Perm.trans (qpartition_loop_perm ..) (Array.swap_perm ..)
    · apply qpartition_loop_perm
  · exact Array.swap_perm ..

theorem qpartition_perm {n} (as : Vector α n) (lt : α → α → Bool) (lo hi : Nat)
    (hlo : lo < n := by omega) (hhi : hi < n := by omega) :
    (qpartition as lt lo hi hlo hhi).2.toArray ~ as.toArray := by
  unfold qpartition
  refine Perm.trans (qpartition_loop_perm ..) ?_
  repeat' first
  | split
  | apply Array.Perm.rfl
  | apply Array.swap_perm
  | refine Perm.trans (Array.swap_perm ..) ?_

theorem qsort_sort_perm {n} (as : Vector α n) (lt : α → α → Bool) (lo hi : Nat) {hlo} {hhi} :
    (qsort.sort lt as lo hi hlo hhi).toArray ~ as.toArray := by
  unfold qsort.sort
  split
  · split
    rename_i as' h
    obtain rfl := (show as' = (qpartition as lt lo hi ..).2 by simp [h])
    split
    · apply qpartition_perm
    · refine Perm.trans (qsort_sort_perm ..) ?_
      refine Perm.trans (qsort_sort_perm ..) ?_
      apply qpartition_perm
  · simp [qpartition]

theorem qsort_perm (as : Array α) (lt : α → α → Bool) (lo hi : Nat) :
    qsort as lt lo hi ~ as := by
  unfold qsort
  split
  · rfl
  · simp [qpartition]
    apply qsort_sort_perm

theorem qpartition_loop_spec₁ {n} (lt : α → α → Bool) (lo hi : Nat)
    (hlo : lo < n := by omega) (hhi : hi < n := by omega)
    {ilo : lo ≤ i} {jh : j < n} {w : i ≤ j} (jhi : j ≤ hi := by omega)
    (as : Vector α n) (hpivot : pivot = as[hi])
    (q : ∀ k, (hk₁ : lo ≤ k) → (hk₂ : k < i) → lt as[k] as[hi]) (mid as')
    (w_mid : mid = (qpartition.loop lt lo hi hhi pivot as i j ilo jh w).1.1)
    (hmid : mid < n)
    (w_as : as' = (qpartition.loop lt lo hi hhi pivot as i j ilo jh w).2) :
    ∀ i, (h₁ : lo ≤ i) → (h₂ : i < mid) → lt as'[i] as'[mid] := by
  unfold qpartition.loop at w_mid w_as
  subst hpivot
  dsimp
  split at w_mid <;> rename_i h₁
  · rw [dif_pos h₁] at w_as
    split at w_mid <;> rename_i h₂
    · rw [if_pos h₂] at w_as
      apply qpartition_loop_spec₁ (w_mid := w_mid) (w_as := w_as)
      · rw [Vector.getElem_swap_of_ne _ _ (by omega) (by omega)]
      intro k hk₁ hk₂
      if hk₂' : k < i then
        specialize q k hk₁ hk₂'
        rwa [Vector.getElem_swap_of_ne _ _ (by omega) (by omega),
          Vector.getElem_swap_of_ne _ _ (by omega) (by omega)]
      else
        obtain rfl := show k = i by omega
        rwa [Vector.getElem_swap_left,
          Vector.getElem_swap_of_ne _ _ (by omega) (by omega)]
    · rw [if_neg h₂] at w_as
      apply qpartition_loop_spec₁ (w_mid := w_mid) (w_as := w_as) (hpivot := rfl) (q := q)
  · rw [dif_neg h₁] at w_as
    subst w_as
    simp [w_mid]
    intro i' hi₁ hi₂
    rw [Vector.getElem_swap_of_ne _ _ (by omega) (by omega)]
    exact q _ hi₁ hi₂

theorem qpartition_loop_spec₂ {n} (lt : α → α → Bool) (lo hi : Nat)
    (hlo : lo < n := by omega) (hhi : hi < n := by omega)
    {ilo : lo ≤ i} {jh : j < n} {w : i ≤ j} (jhi : j ≤ hi := by omega)
    (as : Vector α n) (hpivot : pivot = as[hi])
    (q : ∀ k, (hk₁ : i ≤ k) → (hk₂ : k < j) → !lt as[k] as[hi]) (mid as')
    (w_mid : mid = (qpartition.loop lt lo hi hhi pivot as i j ilo jh w).1.1)
    (hmid : mid < n)
    (w_as : as' = (qpartition.loop lt lo hi hhi pivot as i j ilo jh w).2) :
    ∀ i, (h₁ : mid < i) → (h₂ : i ≤ hi) → !lt as'[i] as'[mid] := by
  unfold qpartition.loop at w_mid w_as
  subst hpivot
  dsimp
  split at w_mid <;> rename_i h₁
  · rw [dif_pos h₁] at w_as
    split at w_mid <;> rename_i h₂
    · rw [if_pos h₂] at w_as
      apply qpartition_loop_spec₂ (w_mid := w_mid) (w_as := w_as)
      · rw [Vector.getElem_swap_of_ne _ _ (by omega) (by omega)]
      intro k hk₁ hk₂
      if hk₂' : k < j then
        specialize q k (by omega) hk₂'
        rwa [Vector.getElem_swap_of_ne _ _ (by omega) (by omega),
          Vector.getElem_swap_of_ne _ _ (by omega) (by omega)]
      else
        obtain rfl := show k = j by omega
        rw [Vector.getElem_swap_right,
          Vector.getElem_swap_of_ne _ _ (by omega) (by omega)]
        exact q i (i.le_refl) (by omega)
    · rw [if_neg h₂] at w_as
      apply qpartition_loop_spec₂ (w_mid := w_mid) (w_as := w_as) (hpivot := rfl)
      intro k hk₁ hk₂
      if hk₂' : k < j then
        exact q k hk₁ hk₂'
      else
        obtain rfl := show k = j by omega
        simp [h₂]
  · rw [dif_neg h₁] at w_as
    subst w_as
    simp [w_mid]
    intro i' hi₁ hi₂
    if hi₂' : i' < hi then
      rw [Vector.getElem_swap_of_ne _ _ (by omega) (by omega)]
      simpa using q i' (by omega) (by omega)
    else
      obtain rfl := show i' = hi by omega
      simpa [hi₂] using q i (by omega) (by omega)

theorem qpartition_spec₁ {n} (lt : α → α → Bool) (lo hi : Nat)
    (hlo : lo < n := by omega) (hhi : hi < n := by omega) (w : lo ≤ hi := by omega)
    (as : Vector α n) (mid as')
    (w_mid : mid = (qpartition as lt lo hi hlo hhi).1.1)
    (hmid : mid < n)
    (w_as : as' = (qpartition as lt lo hi hlo hhi).2) :
    ∀ i, (h₁ : lo ≤ i) → (h₂ : i < mid) → lt as'[i] as'[mid] := by
  unfold qpartition at w_mid w_as
  apply qpartition_loop_spec₁ (w_mid := w_mid) (w_as := w_as) (hpivot := rfl)
  intro k hk₁ hk₂
  omega

theorem qpartition_spec₂ {n} (lt : α → α → Bool) (lo hi : Nat)
    (hlo : lo < n := by omega) (hhi : hi < n := by omega) (w : lo ≤ hi := by omega)
    (as : Vector α n) (mid as')
    (w_mid : mid = (qpartition as lt lo hi hlo hhi).1.1)
    (hmid : mid < n)
    (w_as : as' = (qpartition as lt lo hi hlo hhi).2) :
    ∀ i, (h₁ : mid < i) → (h₂ : i ≤ hi) → !lt as'[i] as'[mid] := by
  unfold qpartition at w_mid w_as
  apply qpartition_loop_spec₂ (w_mid := w_mid) (w_as := w_as) (hpivot := rfl)
  intro k hk₁ hk₂
  omega

theorem size_one_of_hi_le_qpartition_fst {n} (lt : α → α → Bool) (lo hi : Nat)
    (hlo : lo < n := by omega) (hhi : hi < n := by omega)
    (as : Vector α n) (w : hi ≤ (qpartition as lt lo hi hlo hhi).1.1) : n = 1 := by
  unfold qpartition at w
  sorry

theorem qsort_sort_spec {n} (lt : α → α → Bool) (as : Vector α n) (lo hi : Nat)
    (hlo : lo < n := by omega) (hhi : hi < n := by omega) (w : lo ≤ hi := by omega)
    (as' : Vector α n) (w_as : as' = qsort.sort lt as lo hi hlo hhi) :
    ∀ i j, (h₁ : lo ≤ i) → (h₂ : i < j) → (h₃ : j ≤ hi) → lt as'[i] as'[j] := by
  unfold qsort.sort at w_as
  split at w_as <;> rename_i w₁
  · intro i j h₁ h₂ h₃
    split at w_as <;> rename_i mid hmid as'' w₂
    split at w_as <;> rename_i w₃
    · simp only [Prod.ext_iff, Subtype.ext_iff] at w₂
      obtain ⟨rfl, rfl⟩ := w₂
      obtain rfl := size_one_of_hi_le_qpartition_fst _ _ _ _ _ _ w₃
      omega
    · sorry
  · intros
    omega

theorem qsort_sorted' (lt : α → α → Bool) (as : Array α) (lo hi : Nat) :
    ∀ i j, (h₁ : lo ≤ i) → (h₂ : i < j) → (h₃ : j ≤ hi) → (h₄ : j < as.size) →
      lt ((qsort as lt lo hi)[i]'(by simp; omega)) ((qsort as lt lo hi)[j]'(by simp; omega)) := by
  unfold qsort
  intros i j h₁ h₂ h₃ h₄
  split <;> rename_i w
  · omega
  · apply qsort_sort_spec lt as.toVector _ _ (w_as := rfl)
    all_goals omega

theorem qsort_sorted (lt : α → α → Bool) (as : Array α) :
    ∀ i j, (h₁ : i < j) → (h₂ : i < (qsort as lt).size) → (h₃ : j < (qsort as lt).size) →
      lt (qsort as lt)[i] (qsort as lt)[j] := by
  intros i j h₁ h₂ h₃
  simp only [size_qsort] at h₂ h₃
  apply qsort_sorted' _ _ _ _ i j i.zero_le h₁ (by omega) (by omega)

end Array
