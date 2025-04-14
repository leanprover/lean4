/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

-- FIXME: when `grind` is ready for production use, move this file to `src/Init/Data/Array/QSort/Lemmas.lean`.
set_option grind.warning false

/-!
# Verification of `Array.qsort`

This file contains a verification of the `Array.qsort` function,
using the `grind` tactic.

The theorems are:
* `size_qsort : (qsort as lt lo hi).size = as.size`
* `qsort_perm : qsort as lt lo hi ~ as`

And when `lt` is antisymmetric and `¬ lt a b` is transitive, we have:
* `qsort_sorted' : lo ≤ i < j ≤ hi → ¬ lt (as.qsort lt lo hi)[j] (as.qsort lt lo hi)[i]`
* `qsort_sorted : i < j → ¬ lt (as.qsort lt)[j] (as.qsort lt)[i]`

(There is not currently a public theorem that `(qsort as lt lo hi)[i] = as[i]` when `i < lo` or `hi < i`.)

-/
namespace Array

open List Vector

-- These attributes should be moved to the standard library.
attribute [grind] Vector.size_toArray
attribute [grind] Vector.getElem_swap_left Vector.getElem_swap_right
attribute [grind] Vector.getElem_swap_of_ne
attribute [grind] Vector.getElem?_eq_none Vector.getElem?_eq_getElem
attribute [grind] Vector.getElem?_toArray

@[simp, grind] theorem size_qsort (as : Array α) (lt : α → α → Bool) (lo hi : Nat) :
    (qsort as lt lo hi).size = as.size := by
  grind [qsort]

private theorem qpartition_loop_perm {n} (as : Vector α n) (lt : α → α → Bool) (lo hi : Nat)
    {hhi} {ilo} {jh} :
    (qpartition.loop lt lo hi hhi pivot as i j ilo jh w).2.toArray ~ as.toArray := by
  unfold qpartition.loop
  split
  · split
    · exact Perm.trans (qpartition_loop_perm ..) (Array.swap_perm ..)
    · apply qpartition_loop_perm
  · exact Array.swap_perm ..

private theorem qpartition_perm {n} (as : Vector α n) (lt : α → α → Bool) (lo hi : Nat)
    (hlo : lo < n := by omega) (hhi : hi < n := by omega) :
    (qpartition as lt lo hi hlo hhi).2.toArray ~ as.toArray := by
  unfold qpartition
  refine Perm.trans (qpartition_loop_perm ..) ?_
  repeat' first
  | split
  | apply Array.Perm.rfl
  | apply Array.swap_perm
  | refine Perm.trans (Array.swap_perm ..) ?_

private theorem qsort_sort_perm {n} (as : Vector α n) (lt : α → α → Bool) (lo hi : Nat) {hlo} {hhi} :
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

private theorem getElem_qpartition_loop_snd_of_lt_lo {n} (lt : α → α → Bool) (lo hi : Nat)
    (hhi : hi < n) (pivot) (as : Vector α n) (i j) (ilo) (jh) (w : i ≤ j) (w' : lo ≤ hi)
    (k : Nat) (h : k < lo) : (qpartition.loop lt lo hi hhi pivot as i j ilo jh w).2[k] = as[k] := by
  fun_induction qpartition.loop <;> (unfold qpartition.loop; grind)

private theorem getElem_qpartition_snd_of_lt_lo {n} (lt : α → α → Bool) (as : Vector α n) (lo hi : Nat)
    (hlo : lo < n) (hhi : hi < n) (w : lo ≤ hi)
    (k : Nat) (h : k < lo) : (qpartition as lt lo hi hlo hhi).2[k] = as[k] := by
  grind [qpartition, getElem_qpartition_loop_snd_of_lt_lo]

@[local grind] private theorem getElem_qsort_sort_of_lt_lo
    {n} (lt : α → α → Bool) (as : Vector α n) (lo hi : Nat)
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

private theorem getElem_qpartition_loop_snd_of_hi_lt {n} (lt : α → α → Bool) (lo hi : Nat)
    (hhi : hi < n) (pivot) (as : Vector α n) (i j) (ilo) (jh) (w : i ≤ j) (w' : lo ≤ hi) (z : i ≤ hi)
    (k : Nat) (h : hi < k) (h' : k < n) : (qpartition.loop lt lo hi hhi pivot as i j ilo jh w).2[k] = as[k] := by
  fun_induction qpartition.loop <;> (unfold qpartition.loop; grind)

private theorem getElem_qpartition_snd_of_hi_lt {n} (lt : α → α → Bool) (as : Vector α n) (lo hi : Nat)
    (hlo : lo < n) (hhi : hi < n) (w : lo ≤ hi)
    (k : Nat) (h : hi < k) (h' : k < n) : (qpartition as lt lo hi hlo hhi).2[k] = as[k] := by
  grind [qpartition, getElem_qpartition_loop_snd_of_hi_lt]

@[local grind] private theorem getElem_qsort_sort_of_hi_lt
    {n} (lt : α → α → Bool) (as : Vector α n) (lo hi : Nat)
    (hlo : lo < n) (hhi : hi < n) (w : lo ≤ hi)
    (i : Nat) (h : hi < i) (h' : i < n) : (qsort.sort lt as lo hi hlo hhi)[i] = as[i] := by
  unfold qsort.sort
  split
  · simp only []
    split <;> rename_i w₁
    · rw [getElem_qpartition_snd_of_hi_lt] <;> omega
    · change ¬ (?q : { m // lo ≤ m ∧ m < n } × Vector α n).fst.1 ≥ hi at w₁
      have := ?q.1.2.1
      rw [getElem_qsort_sort_of_hi_lt, getElem_qsort_sort_of_hi_lt, getElem_qpartition_snd_of_hi_lt]
      any_goals grind
  · rfl
termination_by hi - lo
decreasing_by all_goals grind

private theorem extract_qsort_sort_perm {n} (as : Vector α n) (lt : α → α → Bool) (lo hi : Nat) (hlo) (hhi) (w : lo ≤ hi) :
    ((qsort.sort lt as lo hi hlo hhi).extract lo (hi + 1)).toArray ~ (as.extract lo (hi + 1)).toArray := by
  apply Array.Perm.extract
  · grind [qsort_sort_perm]
  · grind
  · grind

private theorem getElem_qsort_sort_mem (lt : α → α → Bool)
    (as : Vector α n) (lo hi : Nat)
    (hlo : lo < n := by omega) (hhi : hi < n := by omega)
    (i : Nat) (h : i < n) (_ : lo ≤ i) (_ : i ≤ hi) :
    (qsort.sort lt as lo hi hlo hhi)[i] ∈ as.extract lo (hi + 1) := by
  -- This is horrible!
  have := extract_qsort_sort_perm as lt lo hi hlo hhi (by omega)
  have := Array.Perm.mem_iff this (a := (qsort.sort lt as lo hi hlo hhi)[i])
  rw [← Vector.mem_toArray_iff]
  apply this.mp
  simp
  rw [mem_extract_iff_getElem]
  simp
  refine ⟨i - lo, ?_⟩
  grind

private theorem qpartition_loop_spec₁ {n} (lt : α → α → Bool) (lo hi : Nat)
    (hlo : lo < n := by omega) (hhi : hi < n := by omega)
    {ilo : lo ≤ i} {jh : j < n} {w : i ≤ j} (jhi : j ≤ hi := by omega)
    (as : Vector α n) (hpivot : pivot = as[hi])
    (q : ∀ k, (hk₁ : lo ≤ k) → (hk₂ : k < i) → lt as[k] as[hi]) (mid as')
    (w_mid : mid = (qpartition.loop lt lo hi hhi pivot as i j ilo jh w).fst.1)
    (hmid : mid < n)
    (w_as : as' = (qpartition.loop lt lo hi hhi pivot as i j ilo jh w).2) :
    ∀ i, (h₁ : lo ≤ i) → (h₂ : i < mid) → lt as'[i] as'[mid] := by
  -- FIXME it would be great to use `fun_induction` here, but the goals explode.
  unfold qpartition.loop at w_mid w_as
  subst hpivot
  split at w_mid <;> rename_i h₁
  · rw [dif_pos h₁] at w_as
    split at w_mid <;> rename_i h₂
    · rw [if_pos h₂] at w_as
      apply qpartition_loop_spec₁ (w_mid := w_mid) <;> grind
    · rw [if_neg h₂] at w_as
      apply qpartition_loop_spec₁ (w_mid := w_mid) <;> grind
  · grind

private theorem qpartition_loop_spec₂ {n} (lt : α → α → Bool) (lo hi : Nat)
    (hlo : lo < n := by omega) (hhi : hi < n := by omega)
    {ilo : lo ≤ i} {jh : j < n} {w : i ≤ j} (jhi : j ≤ hi := by omega)
    (as : Vector α n) (hpivot : pivot = as[hi])
    (q : ∀ k, (hk₁ : i ≤ k) → (hk₂ : k < j) → !lt as[k] as[hi]) (mid as')
    (w_mid : mid = (qpartition.loop lt lo hi hhi pivot as i j ilo jh w).fst.1)
    (hmid : mid < n)
    (w_as : as' = (qpartition.loop lt lo hi hhi pivot as i j ilo jh w).2) :
    ∀ i, (h₁ : mid < i) → (h₂ : i ≤ hi) → lt as'[i] as'[mid] = false := by
  -- FIXME it would be great to use `fun_induction` here, but the goals explode.
  unfold qpartition.loop at w_mid w_as
  subst hpivot
  split at w_mid <;> rename_i h₁
  · rw [dif_pos h₁] at w_as
    split at w_mid <;> rename_i h₂
    · rw [if_pos h₂] at w_as
      apply qpartition_loop_spec₂ (w_mid := w_mid) <;> grind
    · rw [if_neg h₂] at w_as
      apply qpartition_loop_spec₂ (w_mid := w_mid) <;> grind
  · grind

/--
All elements in the active range before the pivot, are less than the pivot.
-/
private theorem qpartition_spec₁ {n} (lt : α → α → Bool) (lo hi : Nat)
    (hlo : lo < n := by omega) (hhi : hi < n := by omega) (w : lo ≤ hi := by omega)
    (as : Vector α n) (mid as')
    (w_mid : mid = (qpartition as lt lo hi hlo hhi).fst.1)
    (hmid : mid < n)
    (w_as : as' = (qpartition as lt lo hi hlo hhi).2) :
    ∀ i, (h₁ : lo ≤ i) → (h₂ : i < mid) → lt as'[i] as'[mid] := by
  grind [qpartition, qpartition_loop_spec₁]

/--
All elements in the active range after the pivot, are greater than or equal to the pivot.
-/
private theorem qpartition_spec₂ {n} (lt : α → α → Bool) (lo hi : Nat)
    (hlo : lo < n := by omega) (hhi : hi < n := by omega) (w : lo ≤ hi := by omega)
    (as : Vector α n) (mid as')
    (w_mid : mid = (qpartition as lt lo hi hlo hhi).fst.1)
    (hmid : mid < n)
    (w_as : as' = (qpartition as lt lo hi hlo hhi).2) :
    ∀ i, (h₁ : mid < i) → (h₂ : i ≤ hi) → lt as'[i] as'[mid] = false := by
  grind [qpartition, qpartition_loop_spec₂]

/-!
We now need to deal with a corner case:
we need to show that `qpartition` only returns a value `≥ hi` when `hi ≤ lo`
(and hence the slice of the array between `lo` and `hi` (inclusive) is trivially already sorted).

We prove two preliminary lemmas about `qpartition.loop`.
-/

/-- If we already have `i < j`, then we're sure to return something less than `hi`. -/
private theorem qpartition_loop_lt_hi₁
    (h : lo < hi) (ilo : lo ≤ i) (jh : j < n) (w : i < j) (z : j ≤ hi) :
    (qpartition.loop lt lo hi hhi pivot as i j ilo jh (by omega)).1.val < hi := by
  -- TODO(@nomeata): Can this behaviour of `fun_induction` be improved?
  -- If we specify fewer arguments (in particular, none), `fun_induction` fails with:
  -- "could not find suitable call of 'qpartition.loop' in the goal"
  fun_induction qpartition.loop lt lo hi hhi pivot as i j <;> (unfold qpartition.loop; grind)

/--
Otherwise, if there is some position `j' ≥ j` which is greater than or equal to the pivot,
then when we reach that we'll be sure `i < j`, and hence the previous lemma will apply,
and so we're sure to return something less than `hi`.
 -/
private theorem qpartition_loop_lt_hi₂
    {as : Vector α n} (h : lo < hi) (ilo : lo ≤ i) (jh : j < n) (w : i ≤ j) (z : j ≤ hi) (q : ∃ (j' : Nat) (hj' : j' < n), j' ≥ j ∧ j' < hi ∧ ¬ lt as[j'] pivot) :
    (qpartition.loop lt lo hi hhi pivot as i j ilo jh (by omega)).1.val < hi := by
  fun_induction qpartition.loop with
  | case1 as i j iloi jh w h' h ih =>
    unfold qpartition.loop
    simp [h, h']
    -- FIXME Why can't `grind` do this?
    apply ih <;> grind
  | case2 as i j ilo jh w h' h ih  =>
    unfold qpartition.loop
    grind [qpartition_loop_lt_hi₁]
  | case3 =>
    unfold qpartition.loop
    grind

/-- The only way `qpartition` returns a pivot position `≥ hi` is if `hi ≤ lo`. -/
private theorem hi_le_lo_of_hi_le_qpartition_fst {n} (lt : α → α → Bool) (lt_asymm : ∀ {a b}, lt a b → ¬ lt b a)
    (lo hi : Nat)
    (hlo : lo < n := by omega) (hhi : hi < n := by omega)
    (as : Vector α n) (w : hi ≤ (qpartition as lt lo hi hlo hhi).fst.1) : hi ≤ lo := by
  -- FIXME clean up this proof
  unfold qpartition at w
  apply Decidable.byContradiction
  intro h
  rw [Nat.not_le] at h
  rw [← Nat.not_lt] at w
  apply w; clear w
  lift_lets
  intros mid
  apply qpartition_loop_lt_hi₂ h (z := by omega)
  exact ⟨mid, by grind⟩

private theorem qsort_sort_spec {n}
    (lt : α → α → Bool) (lt_asymm : ∀ {a b}, lt a b → ¬ lt b a)
    (le_trans : ∀ {a b c}, ¬ lt b a → ¬ lt c b → ¬ lt c a)
    (as : Vector α n) (lo hi : Nat)
    (hlo : lo < n := by omega) (hhi : hi < n := by omega) (w : lo ≤ hi := by omega)
    (as' : Vector α n) (w_as : as' = qsort.sort lt as lo hi hlo hhi) :
    ∀ i, (h₁ : lo ≤ i) → (h₂ : i < hi) → ¬ lt as'[i + 1] as'[i] := by
  -- FIXME attempt `fun_induction`?
  unfold qsort.sort at w_as
  split at w_as <;> rename_i w₁
  · intro i h₁ h₂
    split at w_as <;> rename_i mid hmid as' w₂
    split at w_as <;> rename_i w₃
    · simp only [Prod.ext_iff, Subtype.ext_iff] at w₂
      obtain ⟨rfl, rfl⟩ := w₂
      have := hi_le_lo_of_hi_le_qpartition_fst lt lt_asymm _ _ _ _ _ w₃
      grind
    · subst w_as
      if p₁ : i < mid then
        rw [getElem_qsort_sort_of_lt_lo (i := i)]
        rw [getElem_qsort_sort_of_lt_lo (i := i + 1)]
        apply qsort_sort_spec lt lt_asymm le_trans as' lo mid
        all_goals grind
      else
        replace p₁ : mid ≤ i := by omega
        if p₃ : mid = i then
          subst i
          rw [getElem_qsort_sort_of_lt_lo (i := mid)]
          have z := getElem_qsort_sort_mem lt as' lo mid ?_ ?_ mid ?_ ?_ ?_
          rw [Vector.mem_extract_iff_getElem] at z
          obtain ⟨k, hk, z⟩ := z
          rw [← z]
          clear z
          have z := getElem_qsort_sort_mem lt (qsort.sort lt as' lo mid ?_ ?_) (mid + 1) hi ?_ ?_ (mid + 1) ?_ ?_ ?_
          rw [Vector.mem_extract_iff_getElem] at z
          obtain ⟨k', hk', z⟩ := z
          rw [← z]
          clear z
          rw [getElem_qsort_sort_of_hi_lt]
          · by_cases p : lo + k = mid
            · grind [qpartition_spec₂]
            · apply le_trans (b := as'[mid])
              · grind [qpartition_spec₁]
              · grind [qpartition_spec₂]
          all_goals omega
        else
          apply qsort_sort_spec lt lt_asymm le_trans _ _ _ (w_as := rfl) <;> omega
  · grind

/--
The slice of `as.qsort lt lo hi` from `lo` to `hi` (inclusive) is sorted.

This variant states that adjacent elements are non-decreasing.
See `qsort_sorted'` for a variant about arbitrary pairs of indices.
-/
theorem qsort_sorted₁' (lt : α → α → Bool) (lt_asymm : ∀ {a b}, lt a b → ¬ lt b a)
    (le_trans : ∀ {a b c}, ¬ lt b a → ¬ lt c b → ¬ lt c a)
    (as : Array α) (lo hi : Nat) (i) (h₁ : lo ≤ i) (h₂ : i < hi) (h₃ : i + 1 < as.size) :
      ¬ lt ((as.qsort lt lo hi)[i + 1]'(by grind)) ((as.qsort lt lo hi)[i]'(by grind)) := by
  unfold qsort
  split <;> rename_i w
  · grind
  · apply qsort_sort_spec lt lt_asymm le_trans as.toVector _ _ (w_as := rfl) <;> grind

/--
`Array.qsort` returns a sorted array, i.e. adjacent elements are non-decreasing.

See `qsort_sorted` for a variant about arbitrary pairs of indices.
-/
theorem qsort_sorted₁ (lt : α → α → Bool) (lt_asymm : ∀ {a b}, lt a b → ¬ lt b a)
    (le_trans : ∀ {a b c}, ¬ lt b a → ¬ lt c b → ¬ lt c a) (as : Array α)
    (i) (h : i + 1 < (qsort as lt).size) :
    ¬ lt (as.qsort lt)[i + 1] (as.qsort lt)[i] := by
  have := qsort_sorted₁' lt lt_asymm le_trans
  grind

/-- The slice of `as.qsort lt lo hi` from `lo` to `hi` (inclusive) is sorted. -/
theorem qsort_sorted' (lt : α → α → Bool) (lt_asymm : ∀ {a b}, lt a b → ¬ lt b a)
    (le_trans : ∀ {a b c}, ¬ lt b a → ¬ lt c b → ¬ lt c a)
    (as : Array α) (lo hi : Nat) (i j) (h₁ : lo ≤ i) (h₂ : i < j) (h₃ : j ≤ hi) (h₄ : j < as.size) :
      ¬ lt ((as.qsort lt lo hi)[j]'(by grind)) ((as.qsort lt lo hi)[i]'(by grind)) := by
  induction j with
  | zero => grind
  | succ j ih =>
    if p : i = j then
      subst p
      apply qsort_sorted₁' lt lt_asymm le_trans <;> grind
    else
      apply le_trans (b := (as.qsort lt lo hi)[j]'(by grind))
      · grind
      · apply qsort_sorted₁' lt lt_asymm le_trans <;> grind

theorem qsort_sorted (lt : α → α → Bool) (lt_asymm : ∀ {a b}, lt a b → ¬ lt b a)
    (le_trans : ∀ {a b c}, ¬ lt b a → ¬ lt c b → ¬ lt c a) (as : Array α) :
    ∀ i j, (h₁ : i < j) → (h₂ : i < (qsort as lt).size) → (h₃ : j < (qsort as lt).size) →
      ¬ lt (as.qsort lt)[j] (as.qsort lt)[i] := by
  have := qsort_sorted' lt lt_asymm le_trans
  grind

end Array
