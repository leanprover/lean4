/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
-- prelude
-- import Init.Data.Array.QSort.Basic
-- import Init.Data.Array.Perm

set_option grind.warning false

namespace Array

open List Vector

attribute [grind] Vector.size_toArray
attribute [grind] Vector.getElem_swap_left Vector.getElem_swap_right

@[simp, grind] theorem size_qsort (as : Array α) (lt : α → α → Bool) (lo hi : Nat) :
    (qsort as lt lo hi).size = as.size := by
  grind [qsort]

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

grind_pattern qsort_sort_perm => (qsort.sort lt as lo hi hlo hhi).toArray

-- grind_pattern List.Perm.refl => l ~ l -- not working?

theorem qsort_perm (as : Array α) (lt : α → α → Bool) (lo hi : Nat) :
    qsort as lt lo hi ~ as := by
  unfold qsort
  split
  · rfl -- grind won't use `Perm.refl`?
  · grind

attribute [grind] Vector.getElem_swap_of_ne

theorem qpartition_loop_spec₁ {n} (lt : α → α → Bool) (lo hi : Nat)
    (hlo : lo < n := by omega) (hhi : hi < n := by omega)
    {ilo : lo ≤ i} {jh : j < n} {w : i ≤ j} (jhi : j ≤ hi := by omega)
    (as : Vector α n) (hpivot : pivot = as[hi])
    (q : ∀ k, (hk₁ : lo ≤ k) → (hk₂ : k < i) → lt as[k] as[hi]) (mid as')
    (w_mid : mid = (qpartition.loop lt lo hi hhi pivot as i j ilo jh w).fst.1)
    (hmid : mid < n)
    (w_as : as' = (qpartition.loop lt lo hi hhi pivot as i j ilo jh w).2) :
    ∀ i, (h₁ : lo ≤ i) → (h₂ : i < mid) → lt as'[i] as'[mid] := by
  unfold qpartition.loop at w_mid w_as
  subst hpivot
  split at w_mid <;> rename_i h₁
  · rw [dif_pos h₁] at w_as
    split at w_mid <;> rename_i h₂
    · rw [if_pos h₂] at w_as
      apply qpartition_loop_spec₁ (w_mid := w_mid) (w_as := w_as)
      · grind
      grind
    · rw [if_neg h₂] at w_as
      apply qpartition_loop_spec₁ (w_mid := w_mid) (w_as := w_as) (hpivot := rfl) (q := q)
  · grind

theorem qpartition_loop_spec₂ {n} (lt : α → α → Bool) (lo hi : Nat)
    (hlo : lo < n := by omega) (hhi : hi < n := by omega)
    {ilo : lo ≤ i} {jh : j < n} {w : i ≤ j} (jhi : j ≤ hi := by omega)
    (as : Vector α n) (hpivot : pivot = as[hi])
    (q : ∀ k, (hk₁ : i ≤ k) → (hk₂ : k < j) → !lt as[k] as[hi]) (mid as')
    (w_mid : mid = (qpartition.loop lt lo hi hhi pivot as i j ilo jh w).fst.1)
    (hmid : mid < n)
    (w_as : as' = (qpartition.loop lt lo hi hhi pivot as i j ilo jh w).2) :
    ∀ i, (h₁ : mid < i) → (h₂ : i ≤ hi) → !lt as'[i] as'[mid] := by
  unfold qpartition.loop at w_mid w_as
  subst hpivot
  split at w_mid <;> rename_i h₁
  · rw [dif_pos h₁] at w_as
    split at w_mid <;> rename_i h₂
    · rw [if_pos h₂] at w_as
      apply qpartition_loop_spec₂ (w_mid := w_mid) (w_as := w_as)
      · grind
      grind
    · rw [if_neg h₂] at w_as
      apply qpartition_loop_spec₂ (w_mid := w_mid) (w_as := w_as) (hpivot := rfl)
      grind
  · grind

theorem qpartition_spec₁ {n} (lt : α → α → Bool) (lo hi : Nat)
    (hlo : lo < n := by omega) (hhi : hi < n := by omega) (w : lo ≤ hi := by omega)
    (as : Vector α n) (mid as')
    (w_mid : mid = (qpartition as lt lo hi hlo hhi).fst.1)
    (hmid : mid < n)
    (w_as : as' = (qpartition as lt lo hi hlo hhi).2) :
    ∀ i, (h₁ : lo ≤ i) → (h₂ : i < mid) → lt as'[i] as'[mid] := by
  grind [qpartition, qpartition_loop_spec₁]

theorem qpartition_spec₂ {n} (lt : α → α → Bool) (lo hi : Nat)
    (hlo : lo < n := by omega) (hhi : hi < n := by omega) (w : lo ≤ hi := by omega)
    (as : Vector α n) (mid as')
    (w_mid : mid = (qpartition as lt lo hi hlo hhi).fst.1)
    (hmid : mid < n)
    (w_as : as' = (qpartition as lt lo hi hlo hhi).2) :
    ∀ i, (h₁ : mid < i) → (h₂ : i ≤ hi) → !lt as'[i] as'[mid] := by
  grind [qpartition, qpartition_loop_spec₂]

/--
This is an annoying corner case:
we need to show that `qpartition` only returns a value `≥ hi` when `hi ≤ lo`
(and hence the slice of the array between `lo` and `hi` (inclusive) is trivially already sorted).
-/
private theorem hi_le_lo_of_hi_le_qpartition_fst {n} (lt : α → α → Bool) (lo hi : Nat)
    (hlo : lo < n := by omega) (hhi : hi < n := by omega)
    (as : Vector α n) (w : hi ≤ (qpartition as lt lo hi hlo hhi).fst.1) : hi ≤ lo := by
  unfold qpartition at w
  apply Decidable.byContradiction
  intro h
  rw [Nat.not_le] at h
  rw [← Nat.not_lt] at w
  apply w; clear w
  -- We really want `lift_lets` here.
  sorry

theorem getElem_qpartition_loop_snd_of_lt_lo {n} (lt : α → α → Bool) (lo hi : Nat)
    (hhi : hi < n) (pivot) (as : Vector α n) (i j) (ilo) (jh) (w : i ≤ j) (w' : lo ≤ hi)
    (k : Nat) (h : k < lo) : (qpartition.loop lt lo hi hhi pivot as i j ilo jh w).2[k] = as[k] := by
  unfold qpartition.loop
  split
  · split
    · have : hi - (j + 1) < hi - j := by omega
      rw [getElem_qpartition_loop_snd_of_lt_lo (hi := hi) (j := j + 1) (h := h),
        Vector.getElem_swap_of_ne]
      all_goals grind
    · have : hi - (j + 1) < hi - j := by omega
      rw [getElem_qpartition_loop_snd_of_lt_lo (hi := hi) (j := j + 1) (h := h)]
      grind
  · grind
termination_by hi - j

theorem getElem_qpartition_snd_of_lt_lo {n} (lt : α → α → Bool) (as : Vector α n) (lo hi : Nat)
    (hlo : lo < n) (hhi : hi < n) (w : lo ≤ hi)
    (k : Nat) (h : k < lo) : (qpartition as lt lo hi hlo hhi).2[k] = as[k] := by
  unfold qpartition
  rw [getElem_qpartition_loop_snd_of_lt_lo (h := h)]
  · (repeat' split) <;>
    { repeat rw [Vector.getElem_swap_of_ne]
      all_goals grind }

theorem getElem_qsort_sort_of_lt_lo {n} (lt : α → α → Bool) (as : Vector α n) (lo hi : Nat)
    (hlo : lo < n) (hhi : hi < n) (w : lo ≤ hi)
    (i : Nat) (h : i < lo) : (qsort.sort lt as lo hi hlo hhi)[i] = as[i] := by
  unfold qsort.sort
  split
  · simp only []
    split <;> rename_i w₁
    · rw [getElem_qpartition_snd_of_lt_lo] <;> omega
    · change ¬ (?q : { m // lo ≤ m ∧ m < n } × Vector α n).fst.1 ≥ hi at w₁
      have := ?q.1.2.1
      rw [getElem_qsort_sort_of_lt_lo, getElem_qsort_sort_of_lt_lo, getElem_qpartition_snd_of_lt_lo]
      any_goals grind
  · rfl
termination_by hi - lo
decreasing_by all_goals grind

theorem qsort_sort_spec {n} (lt : α → α → Bool) (as : Vector α n) (lo hi : Nat)
    (hlo : lo < n := by omega) (hhi : hi < n := by omega) (w : lo ≤ hi := by omega)
    (as' : Vector α n) (w_as : as' = qsort.sort lt as lo hi hlo hhi) :
    ∀ i j, (h₁ : lo ≤ i) → (h₂ : i < j) → (h₃ : j ≤ hi) → lt as'[i] as'[j] := by
  unfold qsort.sort at w_as
  split at w_as <;> rename_i w₁
  · intro i j h₁ h₂ h₃
    split at w_as <;> rename_i mid hmid as' w₂
    split at w_as <;> rename_i w₃
    · simp only [Prod.ext_iff, Subtype.ext_iff] at w₂
      obtain ⟨rfl, rfl⟩ := w₂
      obtain h := hi_le_lo_of_hi_le_qpartition_fst _ _ _ _ _ _ w₃
      grind
    · sorry
  · grind

example (as : Array α) (lo hi i j : Nat) (h₁ : lo ≤ i) (_ : i < j) (_ : j ≤ hi) (_ : j < as.size)
    (_ : ¬as.size = 0) : min lo (as.size - 1) ≤ i := by
  -- grind -- fails
  omega

/-- The slice of `as.qsort lt lo hi` from `lo` to `hi` (inclusive) is sorted. -/
theorem qsort_sorted' (lt : α → α → Bool) (as : Array α) (lo hi : Nat) :
    ∀ i j, (h₁ : lo ≤ i) → (h₂ : i < j) → (h₃ : j ≤ hi) → (h₄ : j < as.size) →
      lt ((as.qsort lt lo hi)[i]'(by simp; omega)) ((as.qsort lt lo hi)[j]'(by simp; omega)) := by
  unfold qsort
  intros i j h₁ h₂ h₃ h₄
  split <;> rename_i w
  · grind
  · apply qsort_sort_spec lt as.toVector _ _ (w_as := rfl)
    · omega
    · grind
    · omega

theorem qsort_sorted (lt : α → α → Bool) (as : Array α) :
    ∀ i j, (h₁ : i < j) → (h₂ : i < (qsort as lt).size) → (h₃ : j < (qsort as lt).size) →
      lt (as.qsort lt)[i] (as.qsort lt)[j] := by
  grind [qsort_sorted']

end Array
