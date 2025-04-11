/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
-- prelude
-- import Init.Data.Array.QSort.Basic
-- import Init.Data.Array.Perm

set_option grind.warning false

namespace List

namespace Perm

theorem take {l₁ l₂ : List α} (h : l₁ ~ l₂) {n : Nat} (w : l₁.drop n = l₂.drop n) :
    (l₁.take n) ~ (l₂.take n) := by
  rwa [← List.take_append_drop n l₁, ← List.take_append_drop n l₂, w, perm_append_right_iff] at h

theorem drop {l₁ l₂ : List α} (h : l₁ ~ l₂) {n : Nat} (w : l₂.take n = l₁.take n) :
    (l₁.drop n) ~ (l₂.drop n) := by
  rwa [← List.take_append_drop n l₁, ← List.take_append_drop n l₂, w, perm_append_left_iff] at h

theorem take' {l₁ l₂ : List α} (h : l₁ ~ l₂) {n : Nat} (w : ∀ i, n ≤ i → l₁[i]? = l₂[i]?) :
    (l₁.take n) ~ (l₂.take n) := by
  apply h.take
  ext1 i
  simpa using w (n + i) (by omega)

theorem drop' {l₁ l₂ : List α} (h : l₁ ~ l₂) {n : Nat} (w : ∀ i, i < n → l₁[i]? = l₂[i]?) :
    (l₁.drop n) ~ (l₂.drop n) := by
  apply h.drop
  ext1 i
  simp only [getElem?_take]
  split <;> simp_all

def idx [BEq α] {l₁ l₂ : List α} (h : l₁ ~ l₂) (i : Nat) : Nat :=
  match h : l₁[i]? with
  | none => i
  | some x => (l₂.idxOf? x).get (by simp)


end Perm

theorem getElem_of_perm {l₁ l₂ : List α} (h : l₁ ~ l₂) {i : Nat} (w : i < l₁.length) :
    ∃ (j : Nat) (h : j < l₂.length), l₁[i] = l₂[j] := by
  sorry

end List

namespace Array

theorem extract_perm {a b : Array α} (h : a ~ b) (lo hi : Nat)
    (wlo : ∀ i, i < lo → a[i]? = b[i]?) (whi : ∀ i, hi ≤ i → a[i]? = b[i]?) :
    (a.extract lo (hi + 1)) ~ (b.extract lo (hi + 1)) := by
  rcases a with ⟨a⟩
  rcases b with ⟨b⟩
  simp_all only [perm_toArray, List.getElem?_toArray, List.extract_toArray,
    List.extract_eq_drop_take]
  apply List.take_perm' (w := fun i h => by simpa using whi (lo + i) (by omega))
  apply List.drop_perm' (w := wlo)
  exact h

end Array

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

theorem getElem_qsort_sort_of_hi_lt {n} (lt : α → α → Bool) (as : Vector α n) (lo hi : Nat)
    (hlo : lo < n) (hhi : hi < n) (w : lo ≤ hi)
    (i : Nat) (h : hi < i) (h' : i < n) : (qsort.sort lt as lo hi hlo hhi)[i] = as[i] := by
  sorry

theorem extract_qsort_sort_perm {n} (as : Vector α n) (lt : α → α → Bool) (lo hi : Nat) {hlo} {hhi} :
    ((qsort.sort lt as lo hi hlo hhi).extract lo (hi + 1)).toArray ~ (as.extract lo (hi + 1)).toArray := by
  sorry

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

--  theorem qpartition_loop_spec₂' {n} (lt : α → α → Bool) (lo hi : Nat)
--     (hlo : lo < n := by omega) (hhi : hi < n := by omega)
--     {ilo : lo ≤ i} {jh : j < n} {w : i ≤ j} (jhi : j ≤ hi := by omega)
--     (as : Vector α n) (hpivot : pivot = as[hi])
--     (q : ∀ k, (hk₁ : i ≤ k) → (hk₂ : k < j) → !lt as[k] as[hi]) (mid as')
--     (w_mid : mid = (qpartition.loop lt lo hi hhi pivot as i j ilo jh w).fst.1)
--     (hmid : mid < n)
--     (w_as : as' = (qpartition.loop lt lo hi hhi pivot as i j ilo jh w).2) :
--     ∀ i, (h₁ : mid < i) → (h₂ : i ≤ hi) → !lt as'[i] as'[mid] := by
--   fun_induction qpartition.loop with
--   | case1 => sorry
--   | case2 => sorry
--   | case3 => sorry

/--
All elements in the active range before the pivot, are less than the pivot.
-/
theorem qpartition_spec₁ {n} (lt : α → α → Bool) (lo hi : Nat)
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
theorem qpartition_spec₂ {n} (lt : α → α → Bool) (lo hi : Nat)
    (hlo : lo < n := by omega) (hhi : hi < n := by omega) (w : lo ≤ hi := by omega)
    (as : Vector α n) (mid as')
    (w_mid : mid = (qpartition as lt lo hi hlo hhi).fst.1)
    (hmid : mid < n)
    (w_as : as' = (qpartition as lt lo hi hlo hhi).2) :
    ∀ i, (h₁ : mid < i) → (h₂ : i ≤ hi) → !lt as'[i] as'[mid] := by
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
  unfold qpartition.loop
  split <;> rename_i h₁
  · split <;> rename_i h₂
    · apply qpartition_loop_lt_hi₁ h (w := by omega) (z := by omega)
    · apply qpartition_loop_lt_hi₁ h (w := by omega) (z := by omega)
  · simp
    omega

/--
Otherwise, if there is some position `j' ≥ j` which is greater than or equal to the pivot,
then when we reach that we'll be sure `i < j`, and hence the previous lemma will apply,
and so we're sure to return something less than `hi`.
 -/
private theorem qpartition_loop_lt_hi₂
    {as : Vector α n} (h : lo < hi) (ilo : lo ≤ i) (jh : j < n) (w : i ≤ j) (z : j ≤ hi) (q : ∃ (j' : Nat) (hj' : j' < n), j' ≥ j ∧ j' < hi ∧ ¬ lt as[j'] pivot) :
    (qpartition.loop lt lo hi hhi pivot as i j ilo jh (by omega)).1.val < hi := by
  unfold qpartition.loop
  split <;> rename_i h₁
  · split <;> rename_i h₂
    · obtain ⟨j', hj'₁, hj'₂, hj'₃, hj'₄⟩ := q
      have : j ≠ j' := fun h => by simp_all
      apply qpartition_loop_lt_hi₂ h (w := by omega) (z := by omega)
        (q := ⟨j', by omega, by omega, by omega, by
          rw [Vector.getElem_swap_of_ne]
          · exact hj'₄
          · omega
          · omega⟩)
    · apply qpartition_loop_lt_hi₁ h (w := by omega) (z := by omega)
  · simp
    omega
termination_by n - i

/-- The only way `qpartition` returns a pivot position `≥ hi` is if `hi ≤ lo`. -/
private theorem hi_le_lo_of_hi_le_qpartition_fst {n} (lt : α → α → Bool) (lt_asymm : ∀ {a b}, lt a b → ¬ lt b a)
    (lo hi : Nat)
    (hlo : lo < n := by omega) (hhi : hi < n := by omega)
    (as : Vector α n) (w : hi ≤ (qpartition as lt lo hi hlo hhi).fst.1) : hi ≤ lo := by
  unfold qpartition at w
  apply Decidable.byContradiction
  intro h
  rw [Nat.not_le] at h
  rw [← Nat.not_lt] at w
  apply w; clear w
  lift_lets
  intro mid
  intro as₁
  intro as₂
  intro as₃
  intro pivot
  apply qpartition_loop_lt_hi₂ h (z := by omega)
  refine ⟨mid, by omega, by omega, by omega, ?_⟩
  dsimp [pivot, as₃]
  split <;> rename_i h₁
  · rw [Vector.getElem_swap_left, Vector.getElem_swap_right]
    intro h₂
    exact lt_asymm h₂ h₁
  · exact h₁



-- meh, this isn't right. Perhaps don't use an existental?
theorem getElem_qsort_sort(lt : α → α → Bool)
    (as : Vector α n) (lo hi : Nat)
    (hlo : lo < n := by omega) (hhi : hi < n := by omega)
    (i : Nat) (h : i < n) (_ : lo ≤ i) (_ : i ≤ hi) :
    ∃ (j : Nat) (hj : j < n), lo ≤ j ∧ j ≤ hi ∧ (qsort.sort lt as lo hi hlo hhi)[i] = as[j] := by
  sorry

-- def qsort_sort_reindex



theorem qsort_sort_spec₁ {n}
    (lt : α → α → Bool) (lt_asymm : ∀ {a b}, lt a b → ¬ lt b a)
    (le_total : ∀ {a b c}, ¬ lt b a → ¬ lt c b → ¬ lt c a)
    (as : Vector α n) (lo hi : Nat)
    (hlo : lo < n := by omega) (hhi : hi < n := by omega) (w : lo ≤ hi := by omega)
    (as' : Vector α n) (w_as : as' = qsort.sort lt as lo hi hlo hhi) :
    ∀ i, (h₁ : lo ≤ i) → (h₂ : i < hi) → ¬ lt as'[i + 1] as'[i] := by
  unfold qsort.sort at w_as
  split at w_as <;> rename_i w₁
  · intro i h₁ h₂
    split at w_as <;> rename_i mid hmid as' w₂
    split at w_as <;> rename_i w₃
    · simp only [Prod.ext_iff, Subtype.ext_iff] at w₂
      obtain ⟨rfl, rfl⟩ := w₂
      obtain h := hi_le_lo_of_hi_le_qpartition_fst lt lt_asymm _ _ _ _ _ w₃
      grind
    · subst w_as
      if p₁ : i < mid then
        rw [getElem_qsort_sort_of_lt_lo (i := i) (w := by omega) (h := by omega)]
        rw [getElem_qsort_sort_of_lt_lo (i := i + 1) (w := by omega) (h := by omega)]
        apply qsort_sort_spec₁ lt lt_asymm le_total as' lo mid (w_as := rfl)
        all_goals omega
      else
        replace p₁ : mid ≤ i := by omega
        if p₃ : mid = i then
          subst i
          rw [getElem_qsort_sort_of_lt_lo (i := mid) (w := by omega) (h := by omega)]
          sorry
        else
          replace p₃ : mid < i := by omega
          apply qsort_sort_spec₁ lt lt_asymm le_total _ _ _ (w_as := rfl)
          all_goals omega
  · grind

/-- The slice of `as.qsort lt lo hi` from `lo` to `hi` (inclusive) is sorted. -/
theorem qsort_sorted' (lt : α → α → Bool) (lt_asymm : ∀ {a b}, lt a b → ¬ lt b a)
    (le_total : ∀ {a b c}, ¬ lt b a → ¬ lt c b → ¬ lt c a)
    (as : Array α) (lo hi : Nat) :
    ∀ i j, (h₁ : lo ≤ i) → (h₂ : i < j) → (h₃ : j ≤ hi) → (h₄ : j < as.size) →
      ¬ lt ((as.qsort lt lo hi)[j]'(by simp; omega)) ((as.qsort lt lo hi)[i]'(by simp; omega)) := by
  unfold qsort
  intros i j h₁ h₂ h₃ h₄
  split <;> rename_i w
  · grind
  · apply qsort_sort_spec₁ lt lt_asymm le_total as.toVector _ _ (w_as := rfl)
    · omega -- reported in #7810
    · grind
    · omega -- reported in #7810

theorem qsort_sorted (lt : α → α → Bool) (lt_asymm : ∀ {a b}, lt a b → ¬ lt b a)
    (le_total : ∀ {a b c}, ¬ lt b a → ¬ lt c b → ¬ lt c a) (as : Array α) :
    ∀ i j, (h₁ : i < j) → (h₂ : i < (qsort as lt).size) → (h₃ : j < (qsort as lt).size) →
      ¬ lt (as.qsort lt)[j] (as.qsort lt)[i] := by
  have := qsort_sorted' lt lt_asymm le_total
  grind



theorem qsort_sort_spec {n}
    (lt : α → α → Bool) (lt_asymm : ∀ {a b}, lt a b → ¬ lt b a)
    (le_total : ∀ {a b c}, ¬ lt b a → ¬ lt c b → ¬ lt c a)
    (as : Vector α n) (lo hi : Nat)
    (hlo : lo < n := by omega) (hhi : hi < n := by omega) (w : lo ≤ hi := by omega)
    (as' : Vector α n) (w_as : as' = qsort.sort lt as lo hi hlo hhi) :
    ∀ i j, (h₁ : lo ≤ i) → (h₂ : i < j) → (h₃ : j ≤ hi) → ¬ lt as'[j] as'[i] := by
  unfold qsort.sort at w_as
  split at w_as <;> rename_i w₁
  · intro i j h₁ h₂ h₃
    split at w_as <;> rename_i mid hmid as' w₂
    split at w_as <;> rename_i w₃
    · simp only [Prod.ext_iff, Subtype.ext_iff] at w₂
      obtain ⟨rfl, rfl⟩ := w₂
      obtain h := hi_le_lo_of_hi_le_qpartition_fst lt lt_asymm _ _ _ _ _ w₃
      grind
    · subst w_as
      if p₁ : j ≤ mid then
        rw [getElem_qsort_sort_of_lt_lo (i := i) (w := by omega) (h := by omega)]
        rw [getElem_qsort_sort_of_lt_lo (i := j) (w := by omega) (h := by omega)]
        apply qsort_sort_spec lt lt_asymm le_total as' lo mid (w_as := rfl)
        all_goals omega
      else
        replace p₁ : mid < j := by omega
        if p₂ : mid < i then
          apply qsort_sort_spec lt lt_asymm le_total _ (mid + 1) hi (w_as := rfl)
          all_goals omega
        else
          replace p₂ : i ≤ mid := by omega
          -- apply le_total (b := as'[mid])
          if p₃ : i = mid then
            subst i
            rw [getElem_qsort_sort_of_lt_lo (i := mid) (w := by omega) (h := by omega)]
            -- obtain ⟨j', hj'₁ , hj'₂ , hj'₃, w⟩ := getElem_qsort_sort lt (qsort.sort lt as' lo mid ?_ ?_) (mid + 1) hi ?_ ?_ j ?_
            -- rw [w]
            -- We want to use `qpartition_spec₂` here, but ...
            -- we need to know which index to use (there's a permutation above `mid`)
            -- and we need to know `(qsort.sort lt as' lo mid hlo ⋯)[mid]` is just `as'[mid]`
            sorry
          else
            replace p₃ : i < mid := by omega
            apply lt_asymm
            rw [getElem_qsort_sort_of_lt_lo (i := i) (w := by omega) (h := by omega)]
            sorry
  · grind

/-- The slice of `as.qsort lt lo hi` from `lo` to `hi` (inclusive) is sorted. -/
theorem qsort_sorted' (lt : α → α → Bool) (lt_asymm : ∀ {a b}, lt a b → ¬ lt b a)
    (le_total : ∀ {a b c}, ¬ lt b a → ¬ lt c b → ¬ lt c a)
    (as : Array α) (lo hi : Nat) :
    ∀ i j, (h₁ : lo ≤ i) → (h₂ : i < j) → (h₃ : j ≤ hi) → (h₄ : j < as.size) →
      ¬ lt ((as.qsort lt lo hi)[j]'(by simp; omega)) ((as.qsort lt lo hi)[i]'(by simp; omega)) := by
  unfold qsort
  intros i j h₁ h₂ h₃ h₄
  split <;> rename_i w
  · grind
  · apply qsort_sort_spec lt lt_asymm le_total as.toVector _ _ (w_as := rfl)
    · omega -- reported in #7810
    · grind
    · omega -- reported in #7810

theorem qsort_sorted (lt : α → α → Bool) (lt_asymm : ∀ {a b}, lt a b → ¬ lt b a)
    (le_total : ∀ {a b c}, ¬ lt b a → ¬ lt c b → ¬ lt c a) (as : Array α) :
    ∀ i j, (h₁ : i < j) → (h₂ : i < (qsort as lt).size) → (h₃ : j < (qsort as lt).size) →
      ¬ lt (as.qsort lt)[j] (as.qsort lt)[i] := by
  have := qsort_sorted' lt lt_asymm le_total
  grind

end Array
