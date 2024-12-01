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

open List

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
    (hlo : lo < n := by omega) (hhi : hi < n := by omega) {ilo : lo ≤ i} {jh : j < n} {w : i ≤ j}
    (as : Vector α n) (q : ∀ k, (hk₁ : lo ≤ k) → (hk₂ : k < i) → lt as[k] as[hi]) (mid as')
    (w_mid : mid = (qpartition.loop lt lo hi hhi pivot as i j ilo jh w).1.1)
    (hmid : mid < n)
    (w_as : as' = (qpartition.loop lt lo hi hhi pivot as i j ilo jh w).2) :
    ∀ i, (h₁ : lo ≤ i) → (h₂ : i < mid) → lt as'[i] as'[mid] := by
  have hpivot : pivot = as[hi] := by sorry -- have to make this available
  unfold qpartition.loop at w_mid w_as
  dsimp
  split at w_mid <;> rename_i h₁
  · rw [dif_pos h₁] at w_as
    split at w_mid <;> rename_i h₂
    · rw [if_pos h₂] at w_as
      apply qpartition_loop_spec₁ (w_mid := w_mid) (w_as := w_as)
      intro k hk₁ hk₂
      if hk₂' : k < i then
        specialize q k hk₁ hk₂'
        sorry --  okay
        -- rw [Vector.getElem_swap_of_ne]
      else
        obtain rfl := show k = i by omega
        sorry -- okay
    · rw [if_neg h₂] at w_as
      apply qpartition_loop_spec₁ (w_mid := w_mid) (w_as := w_as) (q := q)
  · rw [dif_neg h₁] at w_as
    subst w_as
    simp [w_mid]
    intro i' hi₁ hi₂
    sorry -- okay?


theorem qpartition_spec₁ {n} (lt : α → α → Bool) (lo hi : Nat)
    (hlo : lo < n := by omega) (hhi : hi < n := by omega) (as : Vector α n) (mid as')
    (w_mid : mid = (qpartition as lt lo hi hlo hhi).1.1)
    (hmid : mid < n)
    (w_as : as' = (qpartition as lt lo hi hlo hhi).2) :
    ∀ i, (h₁ : lo ≤ i) → (h₂ : i < mid) → lt as'[i] as'[mid] := by
  unfold qpartition at w_mid w_as
  apply qpartition_loop_spec₁ (w_mid := w_mid) (w_as := w_as)
  intro k hk₁ hk₂
  omega

end Array
