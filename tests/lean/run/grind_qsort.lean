/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

-- TODO: when `grind` is ready for production use, move this file to `src/Init/Data/Array/QSort/Lemmas.lean`.
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

-- Remove after merging master:

attribute [grind] Vector.size_toArray
attribute [grind =] Vector.getElem_swap
attribute [grind] Vector.getElem?_toArray

-- These attributes still need to be moved to the standard library.

-- attribute [grind =] Vector.getElem_swap_of_ne -- Setting `(splits := 9)` means we don't need this

-- set_option trace.grind.ematch.pattern true in
-- attribute [grind] Vector.getElem?_eq_getElem -- This one requires some consideration! -- Probably not need, see Vector.Perm.extract' below.

-- Hmm, we don't seem to have the Array analogues of these!
attribute [grind] Vector.toArray_perm_iff
attribute [grind] Vector.perm_toArray_iff

attribute [grind] Vector.swap_perm

attribute [grind] List.Perm.refl
attribute [grind] Array.Perm.refl
attribute [grind] Vector.Perm.refl

-- attribute [grind] Array.Perm.extract
-- attribute [grind] Vector.Perm.extract

-- These are just the patterns resultin from `grind`, but the behaviour should be explained!
grind_pattern List.Perm.trans => l₁ ~ l₂, l₁ ~ l₃
grind_pattern Array.Perm.trans => xs ~ ys, xs ~ zs
grind_pattern Vector.Perm.trans => xs ~ ys, xs ~ zs

/-- Variant of `List.Perm.take` specifying the the permutation is constant after `i` elementwise. -/
theorem _root_.List.Perm.take_of_getElem {l₁ l₂ : List α} (h : l₁ ~ l₂) {i : Nat}
    (w : ∀ j, i ≤ j → (_ : j < l₁.length) → l₁[j] = l₂[j]'(by have := h.length_eq; omega)) :
    l₁.take i ~ l₂.take i := by
  apply h.take_of_getElem?
  sorry

/-- Variant of `List.Perm.drop` specifying the the permutation is constant before `i` elementwise. -/
theorem _root_.List.Perm.drop_of_getElem {l₁ l₂ : List α} (h : l₁ ~ l₂) {i : Nat}
    (w : ∀ j, j < i → (_ : j < l₁.length) → l₁[j] = l₂[j]'(by have := h.length_eq; omega)) :
    l₁.drop i ~ l₂.drop i := by
  apply h.drop_of_getElem?
  sorry

theorem _root_.Array.Perm.extract' {xs ys : Array α} (h : xs ~ ys) {lo hi : Nat}
    (wlo : ∀ i, i < lo → (_ : i < xs.size) → xs[i] = ys[i]'(by have := h.size_eq; omega))
    (whi : ∀ i, hi ≤ i → (_ : i < xs.size) → xs[i] = ys[i]'(by have := h.size_eq; omega)) :
    xs.extract lo hi ~ ys.extract lo hi := by
  rcases xs with ⟨xs⟩
  rcases ys with ⟨ys⟩
  simp_all only [perm_iff_toList_perm, List.getElem?_toArray, List.extract_toArray,
    List.extract_eq_drop_take]
  apply List.Perm.take_of_getElem (w := fun i h₁ h₂ => by simpa using whi (lo + i) (by omega) sorry)
  apply List.Perm.drop_of_getElem (w := wlo)
  simpa using List.perm_iff_toArray_perm.mpr h

theorem _root_.Vector.Perm.extract' {xs ys : Vector α n} (h : xs ~ ys) {lo hi : Nat}
    (wlo : ∀ i, i < lo → (_ : i < n) → xs[i] = ys[i]) (whi : ∀ i, hi ≤ i → (_ : i < n) → xs[i] = ys[i]) :
    xs.extract lo hi ~ ys.extract lo hi := by
  rcases xs with ⟨xs, rfl⟩
  rcases ys with ⟨ys, h⟩
  exact ⟨Array.Perm.extract' h.toArray (by simpa using wlo) (by simpa using whi)⟩

attribute [grind] Array.Perm.extract'
attribute [grind] Vector.Perm.extract'

@[simp, grind] theorem size_qsort (as : Array α) (lt : α → α → Bool) (lo hi : Nat) :
    (qsort as lt lo hi).size = as.size := by
  grind [qsort]

private theorem qpartition_loop_perm {n} (as : Vector α n) (lt : α → α → Bool) (lo hi : Nat)
    {hhi} {ilo} {jh} :
    (qpartition.loop lt lo hi hhi pivot as i j ilo jh w).2 ~ as := by
  fun_induction qpartition.loop with grind

@[local grind]
private theorem qpartition_perm {n} (as : Vector α n) (lt : α → α → Bool) (lo hi : Nat)
    (hlo : lo < n := by omega) (hhi : hi < n := by omega) :
    (qpartition as lt lo hi hlo hhi).2 ~ as := by
  unfold qpartition
  refine Vector.Perm.trans (qpartition_loop_perm ..) ?_
  repeat' first
  | split
  | grind
  | refine Vector.Perm.trans (Vector.swap_perm ..) ?_

private theorem qsort_sort_perm {n} (as : Vector α n) (lt : α → α → Bool) (lo hi : Nat) {hlo} {hhi} :
    qsort.sort lt as lo hi hlo hhi ~ as := by
  -- TODO: try `fun_induction` here,
  -- but only after `fun_induction` takes care of more unfolding and splitting!
  unfold qsort.sort
  split
  · split
    rename_i as' h
    obtain rfl := (show as' = (qpartition as lt lo hi ..).2 by simp [h])
    split
    · apply qpartition_perm
    · refine Vector.Perm.trans (qsort_sort_perm ..) ?_
      refine Vector.Perm.trans (qsort_sort_perm ..) ?_
      grind
  · grind

grind_pattern qsort_sort_perm => qsort.sort lt as lo hi hlo hhi

theorem qsort_perm (as : Array α) (lt : α → α → Bool) (lo hi : Nat) :
    qsort as lt lo hi ~ as := by
  grind [qsort]

private theorem getElem_qpartition_loop_snd_of_lt_lo {n} (lt : α → α → Bool) (lo hi : Nat)
    (hhi : hi < n) (pivot) (as : Vector α n) (i j) (ilo) (jh) (w : i ≤ j) (w' : lo ≤ hi)
    (k : Nat) (h : k < lo) : (qpartition.loop lt lo hi hhi pivot as i j ilo jh w).2[k] = as[k] := by
  fun_induction qpartition.loop <;> grind

private theorem getElem_qpartition_snd_of_lt_lo {n} (lt : α → α → Bool) (as : Vector α n) (lo hi : Nat)
    (hlo : lo < n) (hhi : hi < n) (w : lo ≤ hi)
    (k : Nat) (h : k < lo) : (qpartition as lt lo hi hlo hhi).2[k] = as[k] := by
  grind (splits := 9) [qpartition, getElem_qpartition_loop_snd_of_lt_lo]

@[local grind] private theorem getElem_qsort_sort_of_lt_lo
    {n} (lt : α → α → Bool) (as : Vector α n) (lo hi : Nat)
    (hlo : lo < n) (hhi : hi < n) (w : lo ≤ hi)
    (i : Nat) (h : i < lo) : (qsort.sort lt as lo hi hlo hhi)[i] = as[i] := by
  fun_induction qsort.sort
  case case1 a b =>
    simp only [dif_pos, *] -- why isn't this handled by grind?
    grind [getElem_qpartition_snd_of_lt_lo]
  case case2 a b ih1 ih2 ih3 =>
    simp only [↓reduceDIte, *] -- insufficient unfolding in qsort.sort.induct_unfolding
    -- This should work from here, but we get "failed to create E-match local theorem" issues
    -- grind [getElem_qpartition_snd_of_lt_lo]
    have := congrArg (·.2) a
    dsimp at this
    subst this
    rw [ih3, ih2, getElem_qpartition_snd_of_lt_lo]
    all_goals grind
  case case3 =>
    grind

private theorem getElem_qpartition_loop_snd_of_hi_lt {n} (lt : α → α → Bool) (lo hi : Nat)
    (hhi : hi < n) (pivot) (as : Vector α n) (i j) (ilo) (jh) (w : i ≤ j) (w' : lo ≤ hi) (z : i ≤ hi)
    (k : Nat) (h : hi < k) (h' : k < n) : (qpartition.loop lt lo hi hhi pivot as i j ilo jh w).2[k] = as[k] := by
  fun_induction qpartition.loop <;> grind

private theorem getElem_qpartition_snd_of_hi_lt {n} (lt : α → α → Bool) (as : Vector α n) (lo hi : Nat)
    (hlo : lo < n) (hhi : hi < n) (w : lo ≤ hi)
    (k : Nat) (h : hi < k) (h' : k < n) : (qpartition as lt lo hi hlo hhi).2[k] = as[k] := by
  grind (splits := 9) [qpartition, getElem_qpartition_loop_snd_of_hi_lt]

@[local grind] private theorem getElem_qsort_sort_of_hi_lt
    {n} (lt : α → α → Bool) (as : Vector α n) (lo hi : Nat)
    (hlo : lo < n) (hhi : hi < n) (w : lo ≤ hi)
    (i : Nat) (h : hi < i) (h' : i < n) : (qsort.sort lt as lo hi hlo hhi)[i] = as[i] := by
  fun_induction qsort.sort
  case case1 a b =>
    simp only [dif_pos, *] -- why isn't this handled by grind?
    grind [getElem_qpartition_snd_of_hi_lt]
  case case2 a b ih1 ih2 ih3 =>
    simp only [↓reduceDIte, *] -- insufficient unfolding in qsort.sort.induct_unfolding
    -- This should work from here, but we get "failed to create E-match local theorem" issues
    -- grind [getElem_qpartition_snd_of_hi_lt]
    have := congrArg (·.2) a
    dsimp at this
    subst this
    rw [ih3, ih2, getElem_qpartition_snd_of_hi_lt]
    all_goals grind
  case case3 =>
    grind

private theorem extract_qsort_sort_perm {n} (as : Vector α n) (lt : α → α → Bool) (lo hi : Nat) (hlo) (hhi) (w : lo ≤ hi) :
    ((qsort.sort lt as lo hi hlo hhi).extract lo (hi + 1)) ~ (as.extract lo (hi + 1)) := by
  grind [qsort_sort_perm]

private theorem getElem_qsort_sort_mem (lt : α → α → Bool)
    (as : Vector α n) (lo hi : Nat)
    (hlo : lo < n := by omega) (hhi : hi < n := by omega)
    (i : Nat) (h : i < n) (_ : lo ≤ i) (_ : i ≤ hi) :
    (qsort.sort lt as lo hi hlo hhi)[i] ∈ as.extract lo (hi + 1) := by
  rw [← (extract_qsort_sort_perm as lt lo hi hlo hhi (by grind)).mem_iff,
    Vector.mem_extract_iff_getElem]
  exact ⟨i - lo, by grind⟩

private theorem qpartition_loop_spec₁ {n} (lt : α → α → Bool) (lo hi : Nat)
    (hlo : lo < n := by omega) (hhi : hi < n := by omega)
    {ilo : lo ≤ i} {jh : j < n} {w : i ≤ j} (jhi : j ≤ hi := by omega)
    (as : Vector α n) (hpivot : pivot = as[hi])
    (q : ∀ k, (hk₁ : lo ≤ k) → (hk₂ : k < i) → lt as[k] as[hi]) (mid as')
    (w_mid : mid = (qpartition.loop lt lo hi hhi pivot as i j ilo jh w).fst.1)
    (hmid : mid < n)
    (w_as : as' = (qpartition.loop lt lo hi hhi pivot as i j ilo jh w).2) :
    ∀ k, (h₁ : lo ≤ k) → (h₂ : k < mid) → lt as'[k] as'[mid] := by
  fun_induction qpartition.loop with unfold qpartition.loop at w_mid w_as
  | case1
  | case2 => apply_assumption <;> grind
  | case3 => grind

private theorem qpartition_loop_spec₂ {n} (lt : α → α → Bool) (lo hi : Nat)
    (hlo : lo < n := by omega) (hhi : hi < n := by omega)
    {ilo : lo ≤ i} {jh : j < n} {w : i ≤ j} (jhi : j ≤ hi := by omega)
    (as : Vector α n) (hpivot : pivot = as[hi])
    (q : ∀ k, (hk₁ : i ≤ k) → (hk₂ : k < j) → !lt as[k] as[hi]) (mid as')
    (w_mid : mid = (qpartition.loop lt lo hi hhi pivot as i j ilo jh w).fst.1)
    (hmid : mid < n)
    (w_as : as' = (qpartition.loop lt lo hi hhi pivot as i j ilo jh w).2) :
    ∀ k, (h₁ : mid < k) → (h₂ : k ≤ hi) → lt as'[k] as'[mid] = false := by
  fun_induction qpartition.loop <;> grind

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
    (h : lo < hi) (ilo : lo ≤ i) (jh : j < n) (w : i < j) (z : j ≤ hi) (h : i ≤ j):
    (qpartition.loop lt lo hi hhi pivot as i j ilo jh h).1.val < hi := by
  fun_induction qpartition.loop <;> grind

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
    apply ih <;> grind -- It would be nice if a more aggressive mode in `grind` would do this.
  | case2 as i j ilo jh w h' h ih  =>
    grind [qpartition_loop_lt_hi₁]
  | case3 =>
    grind

/-- The only way `qpartition` returns a pivot position `≥ hi` is if `hi ≤ lo`. -/
private theorem qpartition_fst_lt_hi {n} (lt : α → α → Bool) (lt_asymm : ∀ {a b}, lt a b → ¬ lt b a)
    (lo hi : Nat)
    (hlo : lo < n := by omega) (hhi : hi < n := by omega)
    (as : Vector α n) (w : lo < hi) : (qpartition as lt lo hi hlo hhi).fst.1 < hi := by
  apply qpartition_loop_lt_hi₂ w
  · grind
  · exact ⟨(lo + hi)/2, by grind⟩

private theorem qsort_sort_spec {n}
    (lt : α → α → Bool) (lt_asymm : ∀ {a b}, lt a b → ¬ lt b a)
    (le_trans : ∀ {a b c}, ¬ lt b a → ¬ lt c b → ¬ lt c a)
    (as : Vector α n) (lo hi : Nat)
    (hlo : lo < n := by omega) (hhi : hi < n := by omega) (w : lo ≤ hi := by omega)
    (as' : Vector α n) (w_as : as' = qsort.sort lt as lo hi hlo hhi) :
    ∀ i, (h₁ : lo ≤ i) → (h₂ : i < hi) → ¬ lt as'[i + 1] as'[i] := by
  unfold qsort.sort at w_as
  split at w_as <;> rename_i w₁
  · -- The interesting case, where `lo < hi`.
    intro i h₁ h₂
    -- Decompose `qpartition as lt lo hi hlo hhi` into `mid` (the pivot) and `as'` (the partitioned array).
    split at w_as <;> rename_i mid hmid as' w₂
    split at w_as <;> rename_i w₃
    · -- If the pivot was at least `hi`, then we get a contradiction from `lo < hi`.
      simp only [Prod.ext_iff, Subtype.ext_iff] at w₂
      obtain ⟨rfl, rfl⟩ := w₂
      have := qpartition_fst_lt_hi lt lt_asymm lo hi hlo hhi as w₁
      grind
    · -- Now we know `lo ≤ mid < hi`.
      subst w_as
      if p₁ : i < mid then
        -- If `i < mid`, then the second stage of sorting is only
        -- moving elements above where we're looking.
        rw [getElem_qsort_sort_of_lt_lo (i := i)]
        rw [getElem_qsort_sort_of_lt_lo (i := i + 1)]
        -- And so we can appply the theorem recursively replacing `hi` with `mid`.
        apply qsort_sort_spec lt lt_asymm le_trans as' lo mid
        -- The remaining arithmetic side conditions are easily resolved.
        all_goals grind
      else
        replace p₁ : mid ≤ i := by omega
        -- If `mid ≤ i`, we need to consider two cases.
        if p₃ : mid = i then
          -- The tricky case, where `mid = i`.
          subst i
          -- On the right hand side, the index is below the range where the second stage of sorting is happening,
          -- so we can drop that sort.
          rw [getElem_qsort_sort_of_lt_lo (i := mid)]
          -- The `mid` element of `qsort.sort lt as' lo mid hlo ⋯`
          -- is *some* element `lo + k` of `as'` in the range `lo ≤ lo + k ≤ mid`.
          have z := getElem_qsort_sort_mem lt as' lo mid ?_ ?_ mid ?_ ?_ ?_
          rw [Vector.mem_extract_iff_getElem] at z
          obtain ⟨k, hk, z⟩ := z
          rw [← z]
          clear z
          -- Similarly, the `mid + 1` element on the left hand side
          -- is some element `mid + 1 + k'` of `qsort.sort lt as' lo mid hlo ⋯`
          -- in the range `mid + 1 ≤ mid + 1 + k' ≤ hi`
          have z := getElem_qsort_sort_mem lt (qsort.sort lt as' lo mid ?_ ?_) (mid + 1) hi ?_ ?_ (mid + 1) ?_ ?_ ?_
          rw [Vector.mem_extract_iff_getElem] at z
          obtain ⟨k', hk', z⟩ := z
          rw [← z]
          clear z
          -- And then the first stage sort on the left hand side can't have any effect,
          -- as it only moves elements between `lo` and `mid` inclusive.
          rw [getElem_qsort_sort_of_hi_lt]
          · by_cases p : lo + k = mid
            · -- Now if `lo + k = mid`,
              -- the element `as'[mid + 1 + k']` is in the top part of the partitioned array,
              -- and `as[lo + k]` is the pivot, so we get the inequality from the specification of `qpartition`.
              grind [qpartition_spec₂]
            · -- Otherwise, we use transitivity:
              -- `as[lo + k']` is in the bottom part, so is strictly less than the pivot,
              -- while `as'[mid + 1 + k']` is in the top, so greater than or equal to the pivot.
              apply le_trans (b := as'[mid])
              · grind [qpartition_spec₁]
              · grind [qpartition_spec₂]
          -- Various arithmetic side conditions remain from the rewriting,
          -- but are now all easy to resolve.
          all_goals grind
        else
          -- If `i < mid`, we can apply the theorem recursively replacing
          -- `as` with `qsort.sort lt as' lo mid hlo ⋯` and `lo` with `mid + 1`.
          apply qsort_sort_spec lt lt_asymm le_trans _ _ _ (w_as := rfl) <;> omega
  · -- Just an arithmetical contradiction.
    grind

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
  · apply qsort_sort_spec lt lt_asymm le_trans (w_as := rfl) <;> grind

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
      apply qsort_sorted₁' <;> grind
    else
      apply le_trans (b := (as.qsort lt lo hi)[j]'(by grind))
      · grind
      · apply qsort_sorted₁' <;> grind

theorem qsort_sorted (lt : α → α → Bool) (lt_asymm : ∀ {a b}, lt a b → ¬ lt b a)
    (le_trans : ∀ {a b c}, ¬ lt b a → ¬ lt c b → ¬ lt c a) (as : Array α) :
    ∀ i j, (h₁ : i < j) → (h₂ : j < (qsort as lt).size) →
      ¬ lt (as.qsort lt)[j] (as.qsort lt)[i] := by
  have := qsort_sorted' lt lt_asymm le_trans
  grind

end Array
