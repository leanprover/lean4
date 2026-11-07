module

import all Lean.ConstTrie
import all Init.Data.Array.QSort.Basic

/-!
Verification of `Lean.ImportedConsts.collectDuplicates`, the import-time sweep for names declared
by several modules. For well-formed module trees, `collectDuplicates_complete` shows that every
name occurring in two modules whose `covered` masks are disjoint is reported with both values,
and `collectDuplicates_sound` that every report lists at least two genuine declarations in
module order. The proofs include a verification of `Array.qsort`, adapted from `grind_qsort.lean`.
-/

/-! ## `Array.qsort` is a sorting permutation -/

namespace Array

open List Vector

-- These attributes still need to be moved to the standard library.

-- Hmm, we don't seem to have the Array analogues of these!
attribute [grind =] Vector.toArray_perm_iff
attribute [grind =] Vector.perm_toArray_iff

attribute [grind .] Vector.swap_perm

attribute [grind .] List.Perm.refl
attribute [grind .] Array.Perm.refl
attribute [grind .] Vector.Perm.refl

-- These are just the patterns resulting from `grind`, but the behaviour should be explained!
grind_pattern List.Perm.trans => l₁ ~ l₂, l₁ ~ l₃
grind_pattern Array.Perm.trans => xs ~ ys, xs ~ zs
grind_pattern Vector.Perm.trans => xs ~ ys, xs ~ zs

/-- Variant of `List.Perm.take` specifying the permutation is constant after `i` elementwise. -/
theorem _root_.List.Perm.take_of_getElem {l₁ l₂ : List α} (h : l₁ ~ l₂) {i : Nat}
    (w : ∀ j, i ≤ j → (_ : j < l₁.length) → l₁[j] = l₂[j]'(by have := h.length_eq; omega)) :
    l₁.take i ~ l₂.take i := by
  apply h.take_of_getElem?
  have := h.length_eq
  grind

/-- Variant of `List.Perm.drop` specifying the permutation is constant before `i` elementwise. -/
theorem _root_.List.Perm.drop_of_getElem {l₁ l₂ : List α} (h : l₁ ~ l₂) {i : Nat}
    (w : ∀ j, j < i → (_ : j < l₁.length) → l₁[j] = l₂[j]'(by have := h.length_eq; omega)) :
    l₁.drop i ~ l₂.drop i := by
  apply h.drop_of_getElem?
  have := h.length_eq
  grind

theorem _root_.Array.Perm.extract' {xs ys : Array α} (h : xs ~ ys) {lo hi : Nat}
    (wlo : ∀ i, i < lo → (_ : i < xs.size) → xs[i] = ys[i]'(by have := h.size_eq; omega))
    (whi : ∀ i, hi ≤ i → (_ : i < xs.size) → xs[i] = ys[i]'(by have := h.size_eq; omega)) :
    xs.extract lo hi ~ ys.extract lo hi := by
  have hs := h.size_eq
  rw [Array.perm_iff_toList_perm] at h ⊢
  simp only [Array.toList_extract, List.extract_eq_take_drop]
  refine List.Perm.take_of_getElem (List.Perm.drop_of_getElem h ?_) ?_ <;> grind

theorem _root_.Vector.Perm.extract' {xs ys : Vector α n} (h : xs ~ ys) {lo hi : Nat}
    (wlo : ∀ i, i < lo → (_ : i < n) → xs[i] = ys[i]) (whi : ∀ i, hi ≤ i → (_ : i < n) → xs[i] = ys[i]) :
    xs.extract lo hi ~ ys.extract lo hi := by
  rcases xs with ⟨xs, rfl⟩
  rcases ys with ⟨ys, h⟩
  exact ⟨Array.Perm.extract' h.toArray (by simpa using wlo) (by simpa using whi)⟩

attribute [grind .] Array.Perm.extract'
attribute [grind .] Vector.Perm.extract'

variable (lt : α → α → Bool) (lo hi : Nat)

@[simp, grind =] theorem size_qsort (as : Array α) :
    (qsort as lt lo hi).size = as.size := by
  grind [qsort]

private theorem qpartition_loop_perm (as : Vector α n)
    (hhi : hi < n) (ilo : lo ≤ i) (ik : i ≤ k) (w : k ≤ hi) :
    (qpartition.loop lt lo hi hhi pivot as i k).2 ~ as := by
  fun_induction qpartition.loop with grind

@[local grind .]
private theorem qpartition_perm
    (as : Vector α n) (w : lo ≤ hi) (hlo : lo < n) (hhi : hi < n) :
    (qpartition as lt lo hi).2 ~ as := by
  unfold qpartition
  refine Vector.Perm.trans (qpartition_loop_perm ..) ?_
  repeat' first
  | split
  | grind
  | refine Vector.Perm.trans (Vector.swap_perm ..) ?_

private theorem qsort_sort_perm
    (as : Vector α n) (w : lo ≤ hi) (hlo : lo < n) (hhi : hi < n) :
    qsort.sort lt as lo hi w hlo hhi ~ as := by
  fun_induction qsort.sort with grind

grind_pattern qsort_sort_perm => qsort.sort lt as lo hi w hlo hhi

theorem qsort_perm (as : Array α) : qsort as lt lo hi ~ as := by
  grind [qsort]

private theorem getElem_qpartition_loop_snd_of_lt_lo
    (hhi : hi < n) (as : Vector α n) (i k : Nat) (ilo : lo ≤ i) (ik : i ≤ k) (w : k ≤ hi) (w' : lo ≤ hi)
    (l : Nat) (h : l < lo) : (qpartition.loop lt lo hi hhi pivot as i k).2[l] = as[l] := by
  fun_induction qpartition.loop <;> grind

private theorem getElem_qpartition_snd_of_lt_lo (as : Vector α n)
    (hhi : hi < n) (w : lo ≤ hi)
    (k : Nat) (h : k < lo) : (qpartition as lt lo hi).2[k] = as[k] := by
  grind [qpartition, getElem_qpartition_loop_snd_of_lt_lo]

@[local grind =] private theorem getElem_qsort_sort_of_lt_lo
    (as : Vector α n)
    (hlo : lo < n) (hhi : hi < n) (w : lo ≤ hi)
    (i : Nat) (h : i < lo) : (qsort.sort lt as lo hi)[i] = as[i] := by
  fun_induction qsort.sort with grind [getElem_qpartition_snd_of_lt_lo]

private theorem getElem_qpartition_loop_snd_of_hi_lt
    (hhi : hi < n) (as : Vector α n) (i k)
    (ilo : lo ≤ i) (ik : i ≤ k) (w : k ≤ hi) (_w' : lo ≤ hi) (z : i ≤ hi)
    (l : Nat) (h : hi < l) (h' : l < n) : (qpartition.loop lt lo hi hhi pivot as i k).2[l] = as[l] := by
  fun_induction qpartition.loop <;> grind

private theorem getElem_qpartition_snd_of_hi_lt (as : Vector α n)
    (hhi : hi < n) (w : lo ≤ hi)
    (k : Nat) (h : hi < k) (h' : k < n) : (qpartition as lt lo hi).2[k] = as[k] := by
  grind [qpartition, getElem_qpartition_loop_snd_of_hi_lt]

@[local grind =] private theorem getElem_qsort_sort_of_hi_lt
    (as : Vector α n) (w : lo ≤ hi)
    (hlo : lo < n) (hhi : hi < n) (w : lo ≤ hi)
    (i : Nat) (h : hi < i) (h' : i < n) : (qsort.sort lt as lo hi)[i] = as[i] := by
  fun_induction qsort.sort with grind [getElem_qpartition_snd_of_hi_lt]

private theorem extract_qsort_sort_perm (as : Vector α n) (lt : α → α → Bool)
    (hlo := by grind) (hhi := by grind) (w : lo ≤ hi := by grind) :
    ((qsort.sort lt as lo hi).extract lo (hi + 1)) ~ (as.extract lo (hi + 1)) := by
  grind

private theorem getElem_qsort_sort_mem
    (as : Vector α n) (hhi : hi < n) (i : Nat) (h : i < n) (_ : lo ≤ i) (_ : i ≤ hi) :
    (qsort.sort lt as lo hi)[i] ∈ as.extract lo (hi + 1) := by
  rw [← (extract_qsort_sort_perm lo hi as lt).mem_iff, Vector.mem_extract_iff_getElem]
  exact ⟨i - lo, by grind⟩

private theorem qpartition_loop_spec₁
    (hhi : hi < n) (ilo : lo ≤ i) (ik : i ≤ k) (w : k < n) (khi : k ≤ hi)
    (as : Vector α n) (hpivot : pivot = as[hi])
    (q : ∀ l, (hk₁ : lo ≤ l) → (hk₂ : l < i) → lt as[l] as[hi]) (mid as')
    (w_mid : mid = (qpartition.loop lt lo hi hhi pivot as i k).fst.1) (hmid : mid < n)
    (w_as : as' = (qpartition.loop lt lo hi hhi pivot as i k).2) :
    ∀ l, (h₁ : lo ≤ l) → (h₂ : l < mid) → lt as'[l] as'[mid] := by
  fun_induction qpartition.loop with unfold qpartition.loop at w_mid w_as
  | case1
  | case2 => apply_assumption <;> grind
  | case3 => grind

private theorem qpartition_loop_spec₂
    (hhi : hi < n) (ilo : lo ≤ i) (ik : i ≤ k) (w : k < n) (khi : k ≤ hi)
    (as : Vector α n) (hpivot : pivot = as[hi])
    (q : ∀ l, (hk₁ : i ≤ l) → (hk₂ : l < k) → !lt as[l] as[hi]) (mid as')
    (w_mid : mid = (qpartition.loop lt lo hi hhi pivot as i k).fst.1) (hmid : mid < n)
    (w_as : as' = (qpartition.loop lt lo hi hhi pivot as i k).2) :
    ∀ l, (h₁ : mid < l) → (h₂ : l ≤ hi) → lt as'[l] as'[mid] = false := by
  fun_induction qpartition.loop with grind

/--
All elements in the active range before the pivot, are less than the pivot.
-/
private theorem qpartition_spec₁
    (hhi : hi < n) (w : lo ≤ hi)
    (as : Vector α n) (mid as')
    (w_mid : mid = (qpartition as lt lo hi).fst.1) (hmid : mid < n)
    (w_as : as' = (qpartition as lt lo hi).2) :
    ∀ i, (h₁ : lo ≤ i) → (h₂ : i < mid) → lt as'[i] as'[mid] := by
  grind [qpartition, qpartition_loop_spec₁]

/--
All elements in the active range after the pivot, are greater than or equal to the pivot.
-/
private theorem qpartition_spec₂
    (hhi : hi < n) (w : lo ≤ hi)
    (as : Vector α n) (mid as')
    (w_mid : mid = (qpartition as lt lo hi).fst.1) (hmid : mid < n)
    (w_as : as' = (qpartition as lt lo hi).2) :
    ∀ i, (h₁ : mid < i) → (h₂ : i ≤ hi) → lt as'[i] as'[mid] = false := by
  grind [qpartition, qpartition_loop_spec₂]

/-!
We now need to deal with a corner case:
we need to show that `qpartition` only returns a value `≥ hi` when `hi ≤ lo`
(and hence the slice of the array between `lo` and `hi` (inclusive) is trivially already sorted).

We prove two preliminary lemmas about `qpartition.loop`.
-/

/-- If we already have `i < k`, then we're sure to return something less than `hi`. -/
private theorem qpartition_loop_lt_hi₁
    (_h : lo < hi) (ilo : lo ≤ i) (ik : i < k) (w : k ≤ hi) (z : k ≤ hi) (ik' : i ≤ k) :
    (qpartition.loop lt lo hi hhi pivot as i k).1.val < hi := by
  fun_induction qpartition.loop with grind

/--
Otherwise, if there is some position `k' ≥ k` which is greater than or equal to the pivot,
then when we reach that we'll be sure `i < k`, and hence the previous lemma will apply,
and so we're sure to return something less than `hi`.
 -/
private theorem qpartition_loop_lt_hi₂
    {as : Vector α n} (h : lo < hi) (ilo : lo ≤ i) (ik : i ≤ k) (w : k < n) (z : k ≤ hi)
    (q : ∃ (k' : Nat) (hj' : k' < n), k' ≥ k ∧ k' < hi ∧ ¬ lt as[k'] pivot) :
    (qpartition.loop lt lo hi hhi pivot as i k).1.val < hi := by
  fun_induction qpartition.loop with
  | case1 =>
    -- It would be nice if a more aggressive mode in `grind` would do this.
    apply_assumption <;> grind
  | case2 => grind [qpartition_loop_lt_hi₁]
  | case3 => grind

/-- The only way `qpartition` returns a pivot position `≥ hi` is if `hi ≤ lo`. -/
private theorem qpartition_fst_lt_hi (lt_asymm : ∀ {a b}, lt a b → ¬ lt b a)
    (as : Vector α n) (hhi : hi < n) (w : lo < hi) : (qpartition as lt lo hi).fst.1 < hi := by
  apply qpartition_loop_lt_hi₂ lt lo hi w
  · grind
  · exact ⟨(lo + hi)/2, by grind⟩

private theorem qsort_sort_spec
    (lt_asymm : ∀ {a b}, lt a b → ¬ lt b a)
    (le_trans : ∀ {a b c}, ¬ lt b a → ¬ lt c b → ¬ lt c a)
    (as : Vector α n) (lo hi : Nat) (hhi : hi < n) (w : lo ≤ hi)
    (as' : Vector α n) (w_as : as' = qsort.sort lt as lo hi) :
    ∀ i, (h₁ : lo ≤ i) → (h₂ : i < hi) → ¬ lt (as')[i + 1] as'[i] := by
  unfold qsort.sort at w_as
  split at w_as <;> rename_i w₁
  · -- The interesting case, where `lo < hi`.
    intro i h₁ h₂
    -- Decompose `qpartition as lt lo hi` into `mid` (the pivot) and `as'` (the partitioned array).
    split at w_as <;> rename_i mid hmid as' w₂
    split at w_as <;> rename_i w₃
    · -- If the pivot was at least `hi`, then we get a contradiction from `lo < hi`.
      simp only [Prod.ext_iff, Subtype.ext_iff] at w₂
      obtain ⟨rfl, rfl⟩ := w₂
      have := qpartition_fst_lt_hi lt lo hi lt_asymm as hhi w₁
      grind
    · -- Now we know `lo ≤ mid < hi`.
      subst w_as
      if p₁ : i < mid then
        -- If `i < mid`, then the second stage of sorting is only
        -- moving elements above where we're looking.
        rw [getElem_qsort_sort_of_lt_lo (i := i)]
        rw [getElem_qsort_sort_of_lt_lo (i := i + 1)]
        -- And so we can apply the theorem recursively replacing `hi` with `mid`.
        apply qsort_sort_spec lt_asymm le_trans as' lo mid
        -- The remaining arithmetic side conditions are easily resolved.
        all_goals grind
      else
        replace p₁ : mid ≤ i := by grind
        -- If `mid ≤ i`, we need to consider two cases.
        if p₃ : mid = i then
          -- The tricky case, where `mid = i`.
          subst i
          -- On the right hand side, the index is below the range where the second stage of sorting is happening,
          -- so we can drop that sort.
          rw [getElem_qsort_sort_of_lt_lo (i := mid)]
          -- The `mid` element of `qsort.sort lt as' lo mid ⋯`
          -- is *some* element `lo + k` of `as'` in the range `lo ≤ lo + k ≤ mid`.
          have z := getElem_qsort_sort_mem lt lo mid as' ?_ mid ?_ ?_ ?_
          rw [Vector.mem_extract_iff_getElem] at z
          obtain ⟨k, hk, z⟩ := z
          rw [← z]
          clear z
          -- Similarly, the `mid + 1` element on the left hand side
          -- is some element `mid + 1 + k'` of `qsort.sort lt as' lo mid ⋯`
          -- in the range `mid + 1 ≤ mid + 1 + k' ≤ hi`
          have z := getElem_qsort_sort_mem lt (mid + 1) hi
            (qsort.sort lt as' lo mid ?_ ?_) ?_ (mid + 1) ?_ ?_ ?_
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
          -- `as` with `qsort.sort lt as' lo mid ⋯` and `lo` with `mid + 1`.
          apply qsort_sort_spec lt_asymm le_trans _ _ _ (w_as := rfl) <;> grind
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

open Lean ImportedConsts

namespace ConstTrieDupSpec

/-! ## `foldChildGroups` groups the candidates' children by key -/

theorem lastPartEq_refl (n : Name) : lastPartEq n n = true := by
  cases n <;> grind [lastPartEq]

theorem lastPartEq_symm {a b : Name} (h : lastPartEq a b = true) : lastPartEq b a = true := by
  cases a <;> cases b <;> grind [lastPartEq]

theorem lastPartEq_trans {a b c : Name} (h₁ : lastPartEq a b = true) (h₂ : lastPartEq b c = true) :
    lastPartEq a c = true := by
  cases a <;> cases b <;> cases c <;> simp_all [lastPartEq]

theorem lastPartEq_of_eq {a b : Name} (h : a = b) : lastPartEq a b = true := h ▸ lastPartEq_refl a

variable {α σ : Type} {cands : Array (Nat × ConstTrie α)}

abbrev Elem (cands : Array (Nat × ConstTrie α)) :=
  UInt64 × Nat × {c : ConstTrie α // IsCandChild cands c}

def pr (x : Elem cands) : Nat × ConstTrie α := (x.2.1, x.2.2.1)

/-- The invariant of `gather` for the run from `a` with hash `h₀`, processed up to `idx`. -/
structure GInv (sorted : Array (Elem cands)) (h₀ : UInt64) (a idx : Nat)
    (groups : Array (Array (Nat × ConstTrie α))) : Prop where
  good : ∀ g ∈ groups, 0 < g.size ∧ g.toList.Sublist ((sorted.toList.map pr).take idx) ∧
    ∀ z ∈ g, z.2.key.hash = h₀ ∧ lastPartEq g[0]!.2.key z.2.key = true
  heads : ∀ k₁ k₂ (h₁ : k₁ < groups.size) (h₂ : k₂ < groups.size),
    lastPartEq groups[k₁][0]!.2.key groups[k₂][0]!.2.key = true → k₁ = k₂
  covers : ∀ m (hm : m < sorted.size), a ≤ m → m < idx → ∃ g ∈ groups, pr sorted[m] ∈ g

theorem getElem!_push_zero {g : Array β} [Inhabited β] (hg : 0 < g.size) (x : β) :
    (g.push x)[0]! = g[0]! := by
  simp [getElem!_pos, Array.getElem_push, *]

theorem take_succ_pr {sorted : Array (Elem cands)} (h : idx < sorted.size) :
    (sorted.toList.map pr).take (idx + 1) =
      (sorted.toList.map pr).take idx ++ [pr sorted[idx]] := by
  rw [List.take_succ_eq_append_getElem (by simpa using h)]; simp

theorem modify_head {groups : Array (Array β)} [Inhabited β] {gi k : Nat} {z : β}
    (hne : ∀ g ∈ groups, 0 < g.size) (hk : k < (groups.modify gi (·.push z)).size) :
    (groups.modify gi (·.push z))[k][0]! = (groups[k]'(by simpa using hk))[0]! := by
  rw [Array.getElem_modify]
  split
  · subst gi; exact getElem!_push_zero (hne _ (Array.getElem_mem _)) z
  · rfl

theorem GInv.modify {sorted : Array (Elem cands)} (hinv : GInv sorted h₀ a idx groups)
    (h : idx < sorted.size) (hzh : (pr sorted[idx]).2.key.hash = h₀) (hgi : gi < groups.size)
    (hlp : lastPartEq groups[gi][0]!.2.key (pr sorted[idx]).2.key = true) :
    GInv sorted h₀ a (idx + 1) (groups.modify gi (·.push (pr sorted[idx]))) := by
  have hne : ∀ g ∈ groups, 0 < g.size := fun g hg => (hinv.good g hg).1
  constructor
  · intro g hg
    obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.mp hg
    simp only [Array.size_modify] at hk
    have hold := hinv.good groups[k] (Array.getElem_mem hk)
    rw [take_succ_pr h, Array.getElem_modify]
    split
    · subst gi
      refine ⟨by simp, by simpa using hold.2.1.append (.refl [pr sorted[idx]]), ?_⟩
      intro z hz
      rw [getElem!_push_zero hold.1]
      rcases Array.mem_push.mp hz with hz | rfl
      · exact hold.2.2 z hz
      · exact ⟨hzh, hlp⟩
    · exact ⟨hold.1, hold.2.1.trans (List.sublist_append_left _ _), hold.2.2⟩
  · intro k₁ k₂ h₁ h₂ hl
    rw [modify_head hne, modify_head hne] at hl
    exact hinv.heads k₁ k₂ _ _ hl
  · intro m hm ha hm'
    by_cases hmi : m = idx
    · exact ⟨_, Array.getElem_mem (i := gi) (by simpa using hgi), by simp [hmi, Array.getElem_modify]⟩
    · obtain ⟨g, hg, hmg⟩ := hinv.covers m hm ha (by omega)
      obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.mp hg
      exact ⟨_, Array.getElem_mem (i := k) (by simpa using hk), by
        rw [Array.getElem_modify]; split <;> simp_all⟩

theorem GInv.push {sorted : Array (Elem cands)} (hinv : GInv sorted h₀ a idx groups)
    (h : idx < sorted.size) (hzh : (pr sorted[idx]).2.key.hash = h₀)
    (hnone : ∀ g ∈ groups, lastPartEq g[0]!.2.key (pr sorted[idx]).2.key = false) :
    GInv sorted h₀ a (idx + 1) (groups.push #[pr sorted[idx]]) := by
  constructor
  · intro g hg
    rw [take_succ_pr h]
    rcases Array.mem_push.mp hg with hg | rfl
    · have hold := hinv.good g hg
      exact ⟨hold.1, hold.2.1.trans (List.sublist_append_left _ _), hold.2.2⟩
    · exact ⟨by simp, by simp, by simp [hzh, lastPartEq_refl]⟩
  · intro k₁ k₂ h₁ h₂ hl
    simp only [Array.size_push] at h₁ h₂
    simp only [Array.getElem_push] at hl
    have hn := fun k (hk : k < groups.size) => hnone groups[k] (Array.getElem_mem hk)
    split at hl <;> split at hl
    · exact hinv.heads k₁ k₂ ‹_› ‹_› hl
    · simp at hl; have := hn k₁ ‹_›; simp_all
    · simp at hl; have := hn k₂ ‹_›; rw [lastPartEq_symm hl] at this; simp at this
    · omega
  · intro m hm ha hm'
    by_cases hmi : m = idx
    · exact ⟨_, Array.mem_push.mpr (.inr rfl), by simp [hmi]⟩
    · obtain ⟨g, hg, hmg⟩ := hinv.covers m hm ha (by omega)
      exact ⟨g, Array.mem_push.mpr (.inl hg), hmg⟩

theorem gather_spec (sorted : Array (Elem cands))
    (hS1 : ∀ k (h : k < sorted.size), sorted[k].1 = sorted[k].2.2.1.key.hash)
    (h₀ : UInt64) (a idx : Nat) (groups) (hg : GroupsOk cands groups)
    (hinv : GInv sorted h₀ a idx groups) (ha : a ≤ idx) (hidx : idx ≤ sorted.size) :
    let r := foldChildGroups.gather cands sorted h₀ idx groups hg
    r.1.2 ≤ sorted.size ∧
    (∀ m (hm : m < sorted.size), idx ≤ m → m < r.1.2 → sorted[m].1 = h₀) ∧
    (∀ hm : r.1.2 < sorted.size, sorted[r.1.2].1 ≠ h₀) ∧
    GInv sorted h₀ a r.1.2 r.1.1 := by
  fun_induction foldChildGroups.gather cands sorted h₀ idx groups hg with
  | case1 idx groups hgroups h hh hash₀ i c heq groups' hgroups' hmatch r hr hidx' hrec ih =>
    rw [hrec] at ih ⊢
    simp only at ih ⊢
    have hS := hS1 idx h
    have hzh : (pr sorted[idx]).2.key.hash = h₀ := by
      simp only [pr]; rw [← hS]; simpa using hh
    have hinv' : GInv sorted h₀ a (idx + 1) groups' := by
      have hpr : pr sorted[idx] = (i, c.1) := by simp [pr, heq]
      split at hmatch <;> rename_i hgi <;> simp only [Subtype.mk.injEq] at hmatch <;>
        subst hmatch <;> rw [← hpr]
      · obtain ⟨hgi, hlp, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp hgi
        exact hinv.modify h hzh hgi (by rwa [hpr])
      · exact hinv.push h hzh (by rw [hpr]; exact Array.findIdx?_eq_none_iff.mp hgi)
    obtain ⟨ih1, ih2, ih3, ih4⟩ := ih hinv' (by omega) (by omega)
    refine ⟨ih1, fun m hm h1 h2 => ?_, ih3, ih4⟩
    rcases Nat.eq_or_lt_of_le h1 with rfl | h1
    · simpa using hh
    · exact ih2 m hm h1 h2
  | case2 idx groups hgroups h hh =>
    simp only
    refine ⟨hidx, fun m hm h1 h2 => by omega, fun _ => by simpa using hh, hinv⟩
  | case3 idx groups hgroups h =>
    refine ⟨hidx, fun m hm h1 h2 => by omega, fun hm => absurd hm h, hinv⟩

section
variable {single : σ → Nat → ConstTrie α → σ}
  {multi : σ → (g : Array (Nat × ConstTrie α)) → 0 < g.size → (∀ x ∈ g, IsCandChild cands x.2) → σ}

theorem flush_inv (Good : Array (Nat × ConstTrie α) → Prop) (Inv : σ → Prop)
    (hs : ∀ s i c, Inv s → Inv (single s i c))
    (hm : ∀ s g h₁ h₂, Inv s → Good g → Inv (multi s g h₁ h₂))
    (groups) (hg : GroupsOk cands groups) (hgood : ∀ g ∈ groups, Good g) (k : Nat) (s : σ)
    (hinv : Inv s) : Inv (foldChildGroups.flush cands single multi groups hg k s) := by
  fun_induction foldChildGroups.flush cands single multi groups hg k s with
  | case1 k s h g hg' ih =>
    apply ih
    split
    · exact hs _ _ _ hinv
    · exact hm _ _ _ _ hinv (hgood _ (Array.getElem_mem h))
  | case2 => exact hinv

theorem two_le_size_of_mem {g : Array β} (hx : x ∈ g) (hy : y ∈ g) (hxy : x ≠ y) : 2 ≤ g.size := by
  rcases g with ⟨_ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> simp_all

theorem flush_complete (Q : σ → Prop)
    (hs : ∀ s i c, Q s → Q (single s i c)) (hm : ∀ s g h₁ h₂, Q s → Q (multi s g h₁ h₂))
    (groups) (hg : GroupsOk cands groups) (m : Nat) (hm' : m < groups.size)
    (hx : x ∈ groups[m]) (hy : y ∈ groups[m]) (hxy : x ≠ y)
    (hQ : ∀ s (h₁ : 0 < groups[m].size) (h₂ : ∀ x ∈ groups[m], IsCandChild cands x.2),
      Q (multi s groups[m] h₁ h₂)) (k : Nat) (hk : k ≤ m) (s : σ) :
    Q (foldChildGroups.flush cands single multi groups hg k s) := by
  fun_induction foldChildGroups.flush cands single multi groups hg k s with
  | case1 k s h g hg' ih =>
    by_cases hkm : k = m
    · subst hkm
      have h2 := two_le_size_of_mem hx hy hxy
      apply flush_inv (fun _ => True) Q (fun s i c h => hs s i c h)
        (fun s g h₁ h₂ h _ => hm s g h₁ h₂ h) groups hg (fun _ _ => trivial)
      split
      · rename_i hc; simp only [g, beq_iff_eq] at hc; omega
      · exact hQ _ _ _
    · exact ih (by omega)
  | case2 k s h => omega

/-- A group passed to `multi` by `go`. -/
def GoodGroup (sorted : Array (Elem cands)) (g : Array (Nat × ConstTrie α)) : Prop :=
  g.toList.Sublist (sorted.toList.map pr) ∧
  ∀ z ∈ g, z.2.key.hash = g[0]!.2.key.hash ∧ lastPartEq g[0]!.2.key z.2.key = true

theorem GInv.goodGroup {sorted : Array (Elem cands)} (hinv : GInv sorted h₀ a idx groups) :
    ∀ g ∈ groups, GoodGroup sorted g := by
  intro g hg
  obtain ⟨hne, hsub, hz⟩ := hinv.good g hg
  refine ⟨hsub.trans (List.take_sublist _ _), fun z hzg => ⟨?_, (hz z hzg).2⟩⟩
  grind

theorem GInv.init {sorted : Array (Elem cands)} (h : idx < sorted.size)
    (hS : (pr sorted[idx]).2.key.hash = h₀) :
    GInv sorted h₀ idx (idx + 1) #[#[pr sorted[idx]]] := by
  constructor
  · intro g hg
    simp only [List.mem_toArray, List.mem_singleton] at hg
    subst hg
    exact ⟨by simp, by rw [take_succ_pr h]; simp, by simp [hS, lastPartEq_refl]⟩
  · intro k₁ k₂ h₁ h₂ _; simp at h₁ h₂; omega
  · intro m hm h₁ h₂
    obtain rfl : m = idx := by omega
    exact ⟨#[pr sorted[m]], by simp, by simp⟩

/-- `gather_spec` for the run that `go` starts at `idx`. -/
theorem gather_spec_start (sorted : Array (Elem cands))
    (hS1 : ∀ k (h : k < sorted.size), sorted[k].1 = sorted[k].2.2.1.key.hash)
    (h : idx < sorted.size) (heq : sorted[idx] = (hash₀, i, c)) :
    let r := foldChildGroups.gather cands sorted hash₀ (idx + 1) #[#[(i, c.1)]]
      (GroupsOk.push (groups := #[]) (by simp [GroupsOk]) (i, c.1) c.2)
    r.1.2 ≤ sorted.size ∧
    (∀ m (hm : m < sorted.size), idx + 1 ≤ m → m < r.1.2 → sorted[m].1 = hash₀) ∧
    (∀ hm : r.1.2 < sorted.size, sorted[r.1.2].1 ≠ hash₀) ∧
    GInv sorted hash₀ idx r.1.2 r.1.1 := by
  have hpr : pr sorted[idx] = (i, c.1) := by simp [pr, heq]
  have hS := hS1 idx h
  rw [heq] at hS
  exact gather_spec sorted hS1 hash₀ idx (idx + 1) _ _
    (by rw [← hpr]; exact GInv.init h (by rw [hpr]; exact hS.symm)) (by omega) (by omega)

theorem go_inv (sorted : Array (Elem cands))
    (hS1 : ∀ k (h : k < sorted.size), sorted[k].1 = sorted[k].2.2.1.key.hash)
    (Inv : σ → Prop)
    (hs : ∀ s i c, Inv s → Inv (single s i c))
    (hm : ∀ s g h₁ h₂, Inv s → GoodGroup sorted g → Inv (multi s g h₁ h₂))
    (idx : Nat) (s : σ) (hinv : Inv s) :
    Inv (foldChildGroups.go cands single multi sorted idx s) := by
  fun_induction foldChildGroups.go cands single multi sorted idx s with
  | case1 idx s h hash₀ i c heq idx₁ h' hh groups idx' hgroups hright hgather ih =>
    have hsp := gather_spec_start sorted hS1 h heq
    rw [hgather] at hsp ⊢
    apply ih
    exact flush_inv (GoodGroup sorted) Inv hs hm groups hgroups hsp.2.2.2.goodGroup 0 s hinv
  | case2 idx s h hash₀ i c heq idx₁ h' hh ih => exact ih (hs _ _ _ hinv)
  | case3 idx s h hash₀ i c heq idx₁ h' ih => exact ih (hs _ _ _ hinv)
  | case4 => exact hinv

theorem sandwich {sorted : Array (Elem cands)}
    (hmono : ∀ p q (hpq : p ≤ q) (hq : q < sorted.size),
      (sorted[p]'(by omega)).1.toNat ≤ sorted[q].1.toNat)
    {a m b : Nat} (ham : a ≤ m) (hmb : m ≤ b) (hb : b < sorted.size)
    (heq : (sorted[a]'(by omega)).1 = sorted[b].1) :
    (sorted[m]'(by omega)).1 = (sorted[a]'(by omega)).1 := by
  have h1 := hmono a m ham (by omega)
  have h2 := hmono m b hmb hb
  have h3 := congrArg UInt64.toNat heq
  apply UInt64.toNat_inj.mp
  omega

theorem go_complete (sorted : Array (Elem cands))
    (hS1 : ∀ k (h : k < sorted.size), sorted[k].1 = sorted[k].2.2.1.key.hash)
    (hmono : ∀ p q (hpq : p ≤ q) (hq : q < sorted.size),
      (sorted[p]'(by omega)).1.toNat ≤ sorted[q].1.toNat)
    (Q : σ → Prop)
    (hs : ∀ s i c, Q s → Q (single s i c)) (hm : ∀ s g h₁ h₂, Q s → Q (multi s g h₁ h₂))
    (p q : Nat) (hp : p < sorted.size) (hq : q < sorted.size)
    (hne : pr sorted[p] ≠ pr sorted[q]) (hkey : (pr sorted[p]).2.key = (pr sorted[q]).2.key)
    (hmulti : ∀ s g h₁ h₂, GoodGroup sorted g → pr sorted[p] ∈ g → pr sorted[q] ∈ g →
      Q (multi s g h₁ h₂))
    (idx : Nat) (s : σ) (hidx : (idx ≤ p ∧ idx ≤ q) ∨ Q s) :
    Q (foldChildGroups.go cands single multi sorted idx s) := by
  have hpq : sorted[p].1 = sorted[q].1 := by
    rw [hS1 p hp, hS1 q hq]; exact congrArg Name.hash hkey
  have hpq' : p ≠ q := by rintro rfl; exact hne rfl
  fun_induction foldChildGroups.go cands single multi sorted idx s with
  | case1 idx s h hash₀ i c heq idx₁ h' hh groups idx' hgroups hright hgather ih =>
    have hsp := gather_spec_start sorted hS1 h heq
    rw [hgather] at hsp ⊢
    apply ih
    obtain ⟨hle, hrun, hend, hginv⟩ := hsp
    simp only at hle hrun hend hginv
    have hidx0 : sorted[idx].1 = hash₀ := by rw [heq]
    rcases hidx with ⟨hip, hiq⟩ | hQs
    · by_cases hhx : hash₀ = sorted[p].1
      · have hlt : ∀ r (hr : r < sorted.size), idx ≤ r → sorted[r].1 = hash₀ → r < idx' := by
          intro r hr h1 h2
          refine Nat.lt_of_not_le fun hcon => hend (by omega) ?_
          rw [sandwich hmono (a := idx) (b := r) (by omega) hcon hr (by rw [hidx0, h2]), hidx0]
        have hpl := hlt p hp hip hhx.symm
        have hql := hlt q hq hiq (by rw [← hpq]; exact hhx.symm)
        obtain ⟨g₁, hg₁, hpg₁⟩ := hginv.covers p hp hip hpl
        obtain ⟨g₂, hg₂, hqg₂⟩ := hginv.covers q hq hiq hql
        obtain ⟨k₁, hk₁, rfl⟩ := Array.mem_iff_getElem.mp hg₁
        obtain ⟨k₂, hk₂, rfl⟩ := Array.mem_iff_getElem.mp hg₂
        obtain rfl : k₁ = k₂ := by
          have e₂ := ((hginv.good _ hg₂).2.2 _ hqg₂).2
          rw [← hkey] at e₂
          exact hginv.heads k₁ k₂ hk₁ hk₂
            (lastPartEq_trans ((hginv.good _ hg₁).2.2 _ hpg₁).2 (lastPartEq_symm e₂))
        right
        exact flush_complete Q hs hm groups hgroups k₁ hk₁ hpg₁ hqg₂ hne
          (fun s h₁ h₂ => hmulti s _ h₁ h₂ (hginv.goodGroup _ hg₁) hpg₁ hqg₂) 0 (Nat.zero_le _) s
      · left
        have hout : ∀ r (hr : r < sorted.size), idx ≤ r → sorted[r].1 = sorted[p].1 → idx' ≤ r := by
          intro r hr h1 h2
          refine Nat.le_of_not_lt fun hcon => hhx ?_
          rcases Nat.eq_or_lt_of_le h1 with rfl | h1
          · rw [← h2, hidx0]
          · rw [← h2, hrun r hr h1 hcon]
        exact ⟨hout p hp hip rfl, hout q hq hiq hpq.symm⟩
    · right
      exact flush_inv (fun _ => True) Q hs (fun s g h₁ h₂ h _ => hm s g h₁ h₂ h) groups hgroups
        (fun _ _ => trivial) 0 s hQs
  | case2 idx s h hash₀ i c heq idx₁ h' hh ih =>
    apply ih
    rcases hidx with ⟨hip, hiq⟩ | hQs
    · left
      have hidx0 : sorted[idx].1 = hash₀ := by rw [heq]
      have key : ∀ b (hb : b < sorted.size), idx < b → sorted[idx].1 ≠ sorted[b].1 := by
        intro b hb hib e
        have := sandwich hmono (m := idx + 1) (Nat.le_succ _) hib hb e
        exact hh (by simpa [hidx0] using this)
      refine ⟨Nat.lt_of_le_of_ne hip fun e => ?_, Nat.lt_of_le_of_ne hiq fun e => ?_⟩ <;> subst e
      · exact key q hq (by omega) hpq
      · exact key p hp (by omega) hpq.symm
    · right; exact hs _ _ _ hQs
  | case3 idx s h hash₀ i c heq idx₁ h' ih =>
    apply ih
    rcases hidx with ⟨hip, hiq⟩ | hQs
    · left
      have : idx₁ = idx + 1 := rfl
      omega
    · right; exact hs _ _ _ hQs
  | case4 idx s h => exact hidx.resolve_left (by omega)

end

def flatPairs (cands : Array (Nat × ConstTrie α)) : List (Nat × ConstTrie α) :=
  cands.toList.flatMap fun p => p.2.children.toList.map fun c => (p.1, c)

def ltE (a b : Elem cands) : Bool := a.1 < b.1 || (a.1 == b.1 && a.2.1 < b.2.1)

theorem foldChildGroups_eq (init : σ) (single : σ → Nat → ConstTrie α → σ)
    (multi : σ → (g : Array (Nat × ConstTrie α)) → 0 < g.size →
      (∀ x ∈ g, IsCandChild cands x.2) → σ) :
    ∃ all : Array (Elem cands),
      foldChildGroups cands init single multi =
        foldChildGroups.go cands single multi (all.qsort ltE) 0 init ∧
      all.toList.map (fun x => (x.1, pr x)) =
        (flatPairs cands).map (fun z => (z.2.key.hash, z)) := by
  refine ⟨_, rfl, ?_⟩
  simp
  rw [show cands.size = cands.attach.size by simp, Array.foldl_append_eq_append]
  change List.map _ (Array.toList (_ ++ Array.flatten _)) = _
  simp [flatPairs, pr, Function.comp_def, List.flatMap]
  exact congrArg _ (List.attach_map_val (f := fun (p : Nat × ConstTrie α) =>
    p.2.children.toList.map fun c => (c.key.hash, p.1, c)))

theorem ltE_iff {a b : Elem cands} :
    ltE a b = true ↔ a.1.toNat < b.1.toNat ∨ (a.1.toNat = b.1.toNat ∧ a.2.1 < b.2.1) := by
  simp only [ltE, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq,
    UInt64.lt_iff_toNat_lt, ← UInt64.toNat_inj]

theorem not_ltE_iff {a b : Elem cands} :
    ¬ ltE b a = true ↔ a.1.toNat < b.1.toNat ∨ (a.1.toNat = b.1.toNat ∧ a.2.1 ≤ b.2.1) := by
  rw [ltE_iff]; omega

theorem ltE_asymm {a b : Elem cands} (h : ltE a b = true) : ¬ ltE b a = true := by
  rw [ltE_iff] at h; rw [not_ltE_iff]; omega

theorem ltE_trans {a b c : Elem cands} (h₁ : ¬ ltE b a = true) (h₂ : ¬ ltE c b = true) :
    ¬ ltE c a = true := by
  rw [not_ltE_iff] at *; omega

theorem sorted_facts (all : Array (Elem cands))
    (hall : all.toList.map (fun x => (x.1, pr x)) =
      (flatPairs cands).map (fun z => (z.2.key.hash, z)))
    (sorted : Array (Elem cands)) (hsd : sorted = all.qsort ltE) :
    (∀ k (h : k < sorted.size), sorted[k].1 = sorted[k].2.2.1.key.hash) ∧
    (∀ p q (hpq : p ≤ q) (hq : q < sorted.size),
      (sorted[p]'(by omega)).1.toNat ≤ sorted[q].1.toNat) ∧
    (sorted.toList.map pr).Perm (flatPairs cands) ∧
    (sorted.toList.map pr).Pairwise (fun a b => a.2.key.hash = b.2.key.hash → a.1 ≤ b.1) := by
  have hperm : sorted.Perm all := hsd ▸ Array.qsort_perm ltE 0 (all.size - 1) all
  have hsorted : ∀ i j (h₁ : i < j) (h₂ : j < sorted.size), ¬ ltE sorted[j] sorted[i] = true := by
    subst hsd; exact Array.qsort_sorted ltE ltE_asymm ltE_trans all
  have hS1 : ∀ k (h : k < sorted.size), sorted[k].1 = sorted[k].2.2.1.key.hash := by
    intro k h
    have hm : sorted[k] ∈ all := hperm.mem_iff.mp (Array.getElem_mem h)
    have : (sorted[k].1, pr sorted[k]) ∈ (flatPairs cands).map (fun z => (z.2.key.hash, z)) := by
      rw [← hall]; exact List.mem_map_of_mem (Array.mem_toList_iff.mpr hm)
    obtain ⟨z, _, hz⟩ := List.mem_map.mp this
    obtain ⟨h1, rfl⟩ := Prod.mk.inj hz
    exact h1.symm
  refine ⟨hS1, ?_, ?_, ?_⟩
  · intro p q hpq hq
    rcases Nat.eq_or_lt_of_le hpq with rfl | h
    · exact Nat.le_refl _
    · have := not_ltE_iff.mp (hsorted p q h hq); omega
  · have h1 : (all.toList.map pr) = flatPairs cands := by
      have := congrArg (List.map Prod.snd) hall
      simpa [Function.comp_def] using this
    rw [← h1]
    exact hperm.toList.map pr
  · rw [List.pairwise_iff_getElem]
    intro i j hi hj hij heq
    simp only [List.length_map, Array.length_toList] at hi hj
    simp only [List.getElem_map, Array.getElem_toList, pr, ← hS1 i hi, ← hS1 j hj] at heq ⊢
    have := not_ltE_iff.mp (hsorted i j hij hj)
    have := congrArg UInt64.toNat heq
    omega

/-- A group passed to `multi` by `foldChildGroups`. -/
def GoodGroup' (cands : Array (Nat × ConstTrie α)) (g : Array (Nat × ConstTrie α)) : Prop :=
  (∃ l : List (Nat × ConstTrie α), l.Perm (flatPairs cands) ∧ g.toList.Sublist l ∧
    l.Pairwise (fun a b => a.2.key.hash = b.2.key.hash → a.1 ≤ b.1)) ∧
  ∀ z ∈ g, z.2.key.hash = g[0]!.2.key.hash ∧ lastPartEq g[0]!.2.key z.2.key = true

section
variable {single : σ → Nat → ConstTrie α → σ}
  {multi : σ → (g : Array (Nat × ConstTrie α)) → 0 < g.size → (∀ x ∈ g, IsCandChild cands x.2) → σ}

theorem foldChildGroups_inv (init : σ) (Inv : σ → Prop) (h₀ : Inv init)
    (hs : ∀ s i c, Inv s → Inv (single s i c))
    (hm : ∀ s g h₁ h₂, Inv s → GoodGroup' cands g → Inv (multi s g h₁ h₂)) :
    Inv (foldChildGroups cands init single multi) := by
  obtain ⟨all, heq, hall⟩ := foldChildGroups_eq init single multi
  obtain ⟨hS1, -, hperm, hpw⟩ := sorted_facts all hall _ rfl
  rw [heq]
  refine go_inv _ hS1 Inv hs (fun s g h₁ h₂ hi hg => hm s g h₁ h₂ hi ?_) 0 init h₀
  exact ⟨⟨_, hperm, hg.1, hpw⟩, hg.2⟩

theorem foldChildGroups_complete (init : σ) (Q : σ → Prop)
    (hs : ∀ s i c, Q s → Q (single s i c)) (hm : ∀ s g h₁ h₂, Q s → Q (multi s g h₁ h₂))
    (x y : Nat × ConstTrie α) (hx : x ∈ flatPairs cands) (hy : y ∈ flatPairs cands) (hxy : x ≠ y)
    (hkey : x.2.key = y.2.key)
    (hmulti : ∀ s g h₁ h₂, GoodGroup' cands g → x ∈ g → y ∈ g → Q (multi s g h₁ h₂)) :
    Q (foldChildGroups cands init single multi) := by
  obtain ⟨all, heq, hall⟩ := foldChildGroups_eq init single multi
  obtain ⟨hS1, hmono, hperm, hpw⟩ := sorted_facts all hall _ rfl
  rw [heq]
  obtain ⟨p, hp, hpx⟩ := List.getElem_of_mem (hperm.mem_iff.mpr hx)
  obtain ⟨q, hq, hqy⟩ := List.getElem_of_mem (hperm.mem_iff.mpr hy)
  simp only [List.getElem_map, Array.getElem_toList, List.length_map, Array.length_toList]
    at hpx hqy hp hq
  subst hpx hqy
  exact go_complete _ hS1 hmono Q hs hm p q hp hq hxy hkey
    (fun s g h₁ h₂ hg hxg hyg => hmulti s g h₁ h₂ ⟨⟨_, hperm, hg.1, hpw⟩, hg.2⟩ hxg hyg) 0 init
    (.inl ⟨Nat.zero_le _, Nat.zero_le _⟩)

end

/-! ## Module trees and the duplicate sweep -/

theorem collectDupsAux_eq (covered : Array UInt64) (key : Name) (cands : Array (Nat × ConstTrie α))
    (acc : Array (Duplicate α)) :
    collectDupsAux covered key cands acc =
      if !covered.isEmpty &&
          cands.foldl (fun c p => c &&& covered[p.1]!) 0xFFFFFFFFFFFFFFFF != 0 then
        acc
      else
        foldChildGroups cands
          (if 1 < (cands.filterMap fun p => p.2.val?.map ((·, p.1))).size then
            acc.push { name := key, entries := cands.filterMap fun p => p.2.val?.map ((·, p.1)) }
          else acc)
          (fun acc _ _ => acc) (fun acc g _ _ => collectDupsAux covered g[0]!.2.key g acc) := by
  rw [collectDupsAux]
  by_cases hc : covered.isEmpty <;> simp [hc] <;> repeat' split
  all_goals rfl

theorem and_self_left' (a b : UInt64) : a &&& (a &&& b) = a &&& b := by
  rw [← UInt64.and_assoc, UInt64.and_self]

theorem foldl_and_le (l : List β) (f : β → UInt64) (init : UInt64) :
    (l.foldl (fun c p => c &&& f p) init) &&& init = l.foldl (fun c p => c &&& f p) init ∧
    ∀ x ∈ l,
      (l.foldl (fun c p => c &&& f p) init) &&& f x = l.foldl (fun c p => c &&& f p) init := by
  induction l generalizing init with
  | nil => simp [UInt64.and_self]
  | cons a l ih =>
    obtain ⟨ih₁, ih₂⟩ := ih (init &&& f a)
    simp only [List.foldl_cons, List.mem_cons, forall_eq_or_imp]
    generalize List.foldl (fun c p => c &&& f p) (init &&& f a) l = r at *
    exact ⟨by grind, by grind, ih₂⟩

/-- The pruning test never fires when two of the candidates have disjoint masks. -/
theorem not_pruned (covered : Array UInt64) (cands : Array (Nat × ConstTrie α))
    (hi : (i, ti) ∈ cands) (hj : (j, tj) ∈ cands) (h : covered[i]! &&& covered[j]! = 0) :
    cands.foldl (fun c p => c &&& covered[p.1]!) 0xFFFFFFFFFFFFFFFF = 0 := by
  rw [← Array.foldl_toList]
  have := (foldl_and_le cands.toList (fun p => covered[p.1]!) 0xFFFFFFFFFFFFFFFF).2
  have h₁ := this _ (Array.mem_toList_iff.mpr hi)
  have h₂ := this _ (Array.mem_toList_iff.mpr hj)
  simp only at h₁ h₂
  generalize List.foldl _ _ _ = r at *
  rw [← h₁, ← h₂]
  rw [← h₂] at h₁
  calc r &&& covered[j]! &&& covered[i]! = r &&& (covered[i]! &&& covered[j]!) := by ac_rfl
    _ = 0 := by rw [h, UInt64.and_zero]

/-- `c` extends `k` by exactly one component. -/
def ExtendsOne (k c : Name) : Prop := (∃ s, c = k.str s) ∨ (∃ n, c = k.num n)

/--
A well-formed module tree: every child's key extends its parent's key by one component, and the
children of a node have pairwise distinct keys.
-/
inductive WF : ConstTrie α → Prop
  | intro (t : ConstTrie α)
      (keys : ∀ c ∈ t.children, ExtendsOne t.key c.key)
      (distinct : t.children.toList.Pairwise (fun c₁ c₂ => c₁.key ≠ c₂.key))
      (children : ∀ c ∈ t.children, WF c) : WF t

/-- `Has t n v`: the tree `t` maps the name `n` to `v`. -/
inductive Has : ConstTrie α → Name → α → Prop
  | here {t : ConstTrie α} {v : α} : t.val? = some v → Has t t.key v
  | child {t c : ConstTrie α} {n : Name} {v : α} : c ∈ t.children → Has c n v → Has t n v

def depth : Name → Nat
  | .anonymous => 0
  | .str p _ => depth p + 1
  | .num p _ => depth p + 1

/-- Removes the last component. -/
def parent : Name → Name
  | .anonymous => .anonymous
  | .str p _ => p
  | .num p _ => p

/-- Removes the last `m` components. -/
def dropN (n : Name) : Nat → Name
  | 0 => n
  | m + 1 => parent (dropN n m)

theorem depth_parent (n : Name) : depth (parent n) = depth n - 1 := by
  cases n <;> simp [depth, parent]

theorem depth_dropN (n : Name) (m : Nat) : depth (dropN n m) = depth n - m := by
  induction m <;> grind [dropN, depth_parent]

theorem ExtendsOne.depth (h : ExtendsOne k c) : depth c = depth k + 1 := by
  rcases h with ⟨s, rfl⟩ | ⟨n, rfl⟩ <;> rfl

theorem ExtendsOne.parent (h : ExtendsOne k c) : parent c = k := by
  rcases h with ⟨s, rfl⟩ | ⟨n, rfl⟩ <;> rfl

theorem ExtendsOne.eq_of_lastPartEq (ha : ExtendsOne k a) (hb : ExtendsOne k b)
    (h : lastPartEq a b = true) : a = b := by
  rcases ha with ⟨s, rfl⟩ | ⟨n, rfl⟩ <;> rcases hb with ⟨s', rfl⟩ | ⟨n', rfl⟩ <;>
    simp_all [lastPartEq]

theorem WF.keys {t : ConstTrie α} (h : WF t) : ∀ c ∈ t.children, ExtendsOne t.key c.key := by
  cases h; assumption

theorem WF.distinct {t : ConstTrie α} (h : WF t) :
    t.children.toList.Pairwise (fun c₁ c₂ => c₁.key ≠ c₂.key) := by
  cases h; assumption

theorem WF.child {t c : ConstTrie α} (h : WF t) (hc : c ∈ t.children) : WF c := by
  cases h with | intro _ _ _ h => exact h c hc

/-- A key reachable in `t` is `t.key` extended by some components. -/
theorem Has.exists_dropN {t : ConstTrie α} (hwf : WF t) (h : Has t n v) :
    ∃ m, dropN n m = t.key := by
  induction h with
  | here => exact ⟨0, rfl⟩
  | @child t c n v hc _ ih =>
    obtain ⟨m, hm⟩ := ih (hwf.child hc)
    exact ⟨m + 1, by simp only [dropN, hm, (hwf.keys c hc).parent]⟩

theorem Has.depth_le {t : ConstTrie α} (hwf : WF t) (h : Has t n v) : depth t.key ≤ depth n := by
  obtain ⟨m, hm⟩ := h.exists_dropN hwf
  grind [depth_dropN]

/-- In a well-formed tree, a value for the tree's own key is stored in its root. -/
theorem Has.val_of_key {t : ConstTrie α} (hwf : WF t) (h : Has t t.key v) : t.val? = some v := by
  cases h with
  | here h => exact h
  | child hc h =>
    have := h.depth_le (hwf.child hc)
    have := (hwf.keys _ hc).depth
    omega

/-- Children of nodes with the same key reaching the same name have the same key. -/
theorem child_key_eq {ti tj ci cj : ConstTrie α} (hwi : WF ti) (hwj : WF tj) (hk : ti.key = tj.key)
    (hci : ci ∈ ti.children) (hcj : cj ∈ tj.children) (hi : Has ci n vi) (hj : Has cj n vj) :
    ci.key = cj.key := by
  obtain ⟨mi, hmi⟩ := hi.exists_dropN (hwi.child hci)
  obtain ⟨mj, hmj⟩ := hj.exists_dropN (hwj.child hcj)
  have := (hwi.keys _ hci).depth
  have := (hwj.keys _ hcj).depth
  obtain rfl : mi = mj := by grind [depth_dropN]
  rw [← hmi, ← hmj]

theorem eq_of_pairwise_ne {f : β → γ} {l : List β} (h : l.Pairwise (fun a b => f a ≠ f b))
    (ha : a ∈ l) (hb : b ∈ l) (hab : f a = f b) : a = b := by
  induction l with
  | nil => simp at ha
  | cons x l ih => grind [List.pairwise_cons]

/-- In a well-formed tree, a name has at most one value. -/
theorem Has.unique {t : ConstTrie α} (hwf : WF t) (h : Has t n v) (h' : Has t n v') : v = v' := by
  induction h with
  | here hv => exact Option.some.inj (hv.symm.trans (Has.val_of_key hwf h'))
  | @child t c n v hc hcv ih =>
    cases h' with
    | here =>
      have := hcv.depth_le (hwf.child hc)
      have := (hwf.keys _ hc).depth
      omega
    | child hc' hcv' =>
      have hk := child_key_eq hwf hwf rfl hc hc' hcv hcv'
      have := eq_of_pairwise_ne hwf.distinct (Array.mem_toList_iff.mpr hc)
        (Array.mem_toList_iff.mpr hc') hk
      subst this
      exact ih (hwf.child hc) hcv'

theorem mem_flatPairs {cands : Array (Nat × ConstTrie α)} :
    z ∈ flatPairs cands ↔ ∃ t, (z.1, t) ∈ cands ∧ z.2 ∈ t.children := by
  rcases z with ⟨i, c⟩
  simp [flatPairs, @exists_comm Nat]

theorem collectDupsAux_mono (covered : Array UInt64) (key : Name)
    (cands : Array (Nat × ConstTrie α))
    (acc : Array (Duplicate α)) (d : Duplicate α) (hd : d ∈ acc) :
    d ∈ collectDupsAux covered key cands acc := by
  rw [collectDupsAux_eq]
  split
  · exact hd
  · apply foldChildGroups_inv _ (d ∈ ·)
    · split
      · exact Array.mem_push.mpr (.inl hd)
      · exact hd
    · exact fun _ _ _ h => h
    · exact fun s g h₁ h₂ hs _ => collectDupsAux_mono covered _ g s d hs
termination_by maxSize cands
decreasing_by exact maxSize_lt h₁ h₂

theorem GoodGroup'.mem_flat {cands g : Array (Nat × ConstTrie α)} (hg : GoodGroup' cands g)
    (hz : z ∈ g) : z ∈ flatPairs cands := by
  obtain ⟨⟨l, hperm, hsub, -⟩, -⟩ := hg
  exact hperm.mem_iff.mp (hsub.subset (Array.mem_toList_iff.mpr hz))

theorem GoodGroup'.wf {cands g : Array (Nat × ConstTrie α)} (hg : GoodGroup' cands g)
    (hne : 0 < g.size) (hwf : ∀ p ∈ cands, WF p.2 ∧ p.2.key = K) :
    ∀ z ∈ g, WF z.2 ∧ z.2.key = g[0]!.2.key := by
  have hext : ∀ z ∈ g, WF z.2 ∧ ExtendsOne K z.2.key := by
    intro z hz
    obtain ⟨t, ht, hc⟩ := mem_flatPairs.mp (hg.mem_flat hz)
    have := hwf _ ht
    exact ⟨this.1.child hc, this.2 ▸ this.1.keys _ hc⟩
  have h0 : g[0]! ∈ g := by
    rw [getElem!_pos g 0 hne]; exact Array.getElem_mem hne
  intro z hz
  refine ⟨(hext z hz).1, ?_⟩
  exact ((hext _ h0).2.eq_of_lastPartEq (hext z hz).2 (hg.2 z hz).2).symm

theorem collectDupsAux_complete (covered : Array UInt64) (K : Name)
    (cands : Array (Nat × ConstTrie α)) (acc : Array (Duplicate α))
    (hwf : ∀ p ∈ cands, WF p.2 ∧ p.2.key = K)
    (hi : (i, ti) ∈ cands) (hj : (j, tj) ∈ cands) (hij : i ≠ j)
    (hvi : Has ti n vi) (hvj : Has tj n vj)
    (hcov : covered.isEmpty ∨ covered[i]! &&& covered[j]! = 0) :
    ∃ d ∈ collectDupsAux covered K cands acc,
      d.name = n ∧ (vi, i) ∈ d.entries ∧ (vj, j) ∈ d.entries := by
  have hnp : ¬(!covered.isEmpty &&
      cands.foldl (fun c p => c &&& covered[p.1]!) 0xFFFFFFFFFFFFFFFF != 0) = true := by
    rcases hcov with h | h <;> simp [h, not_pruned covered cands hi hj]
  rw [collectDupsAux_eq, ite_eq_right_of_eq_false _ _ (eq_false hnp)]
  have hQm : ∀ s g (h₁ : 0 < g.size) (h₂ : ∀ x ∈ g, IsCandChild cands x.2),
      (∃ d ∈ s, d.name = n ∧ (vi, i) ∈ d.entries ∧ (vj, j) ∈ d.entries) →
      (∃ d ∈ collectDupsAux covered g[0]!.2.key g s,
        d.name = n ∧ (vi, i) ∈ d.entries ∧ (vj, j) ∈ d.entries) := by
    rintro s g - - ⟨d, hd, hdn⟩
    exact ⟨d, collectDupsAux_mono _ _ _ _ _ hd, hdn⟩
  by_cases hn : n = K
  · subst hn
    have hei : (vi, i) ∈ cands.filterMap fun p => p.2.val?.map ((·, p.1)) :=
      Array.mem_filterMap.mpr ⟨_, hi, by simp [Has.val_of_key (hwf _ hi).1 ((hwf _ hi).2 ▸ hvi)]⟩
    have hej : (vj, j) ∈ cands.filterMap fun p => p.2.val?.map ((·, p.1)) :=
      Array.mem_filterMap.mpr ⟨_, hj, by simp [Has.val_of_key (hwf _ hj).1 ((hwf _ hj).2 ▸ hvj)]⟩
    have h2 := two_le_size_of_mem hei hej (by simp [hij])
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
    exact foldChildGroups_inv _
      (fun (s : Array (Duplicate α)) =>
        ∃ d ∈ s, d.name = n ∧ (vi, i) ∈ d.entries ∧ (vj, j) ∈ d.entries)
      ⟨_, Array.mem_push.mpr (.inr rfl), rfl, hei, hej⟩ (fun s i c h => h)
      (fun s g h₁ h₂ h _ => hQm s g h₁ h₂ h)
  · have hchild : ∀ {t : ConstTrie α} {v}, t.key = K → Has t n v →
        ∃ c ∈ t.children, Has c n v := by
      intro t v hk h
      cases h with
      | here => exact absurd hk hn
      | child hc h => exact ⟨_, hc, h⟩
    obtain ⟨ci, hci, hvci⟩ := hchild (hwf _ hi).2 hvi
    obtain ⟨cj, hcj, hvcj⟩ := hchild (hwf _ hj).2 hvj
    have hkey := child_key_eq (hwf _ hi).1 (hwf _ hj).1 ((hwf _ hi).2.trans (hwf _ hj).2.symm)
      hci hcj hvci hvcj
    apply foldChildGroups_complete _
      (fun (s : Array (Duplicate α)) =>
        ∃ d ∈ s, d.name = n ∧ (vi, i) ∈ d.entries ∧ (vj, j) ∈ d.entries)
      (fun s i c h => h) hQm (i, ci) (j, cj) (mem_flatPairs.mpr ⟨_, hi, hci⟩)
      (mem_flatPairs.mpr ⟨_, hj, hcj⟩) (by simp [hij]) hkey
    intro s g h₁ h₂ hg hxg hyg
    exact collectDupsAux_complete covered _ g s (hg.wf h₁ hwf) hxg hyg hij hvci hvcj hcov
termination_by maxSize cands
decreasing_by exact maxSize_lt h₁ h₂

/-- A reported duplicate is genuine: at least two entries, each a module's value for the name. -/
def Sound (trees : Array (Nat × ConstTrie α)) (d : Duplicate α) : Prop :=
  2 ≤ d.entries.size ∧ (∀ e ∈ d.entries, ∃ t, (e.2, t) ∈ trees ∧ Has t d.name e.1) ∧
    d.entries.toList.Pairwise (fun a b => a.2 < b.2)

theorem flatPairs_nodup {cands : Array (Nat × ConstTrie α)} (hwf : ∀ p ∈ cands, WF p.2)
    (hord : cands.toList.Pairwise (fun a b => a.1 < b.1)) : (flatPairs cands).Nodup := by
  unfold flatPairs List.Nodup
  rw [List.pairwise_flatMap]
  refine ⟨fun p hp => ?_, hord.imp fun h x hx y hy => ?_⟩
  · rw [List.pairwise_map]
    exact (hwf p (Array.mem_toList_iff.mp hp)).distinct.imp fun h e => h (by simp at e; rw [e])
  · simp only [List.mem_map] at hx hy
    obtain ⟨_, _, rfl⟩ := hx
    obtain ⟨_, _, rfl⟩ := hy
    intro e; simp at e; omega

theorem GoodGroup'.ordered {cands g : Array (Nat × ConstTrie α)} (hg : GoodGroup' cands g)
    (hne : 0 < g.size) (hwf : ∀ p ∈ cands, WF p.2 ∧ p.2.key = K)
    (hord : cands.toList.Pairwise (fun a b => a.1 < b.1)) :
    g.toList.Pairwise (fun a b => a.1 < b.1) := by
  have hkeys := hg.wf hne hwf
  have ⟨⟨l, hperm, hsub, hpw⟩, hhash⟩ := hg
  have hnd : g.toList.Nodup :=
    hsub.nodup (hperm.nodup_iff.mpr (flatPairs_nodup (fun p hp => (hwf p hp).1) hord))
  have hle : g.toList.Pairwise (fun a b => a.1 ≤ b.1) := by
    refine (hpw.sublist hsub).imp_of_mem fun ha hb h => h ?_
    rw [(hhash _ (Array.mem_toList_iff.mp ha)).1, (hhash _ (Array.mem_toList_iff.mp hb)).1]
  refine (hle.and hnd).imp_of_mem fun {a b} ha hb ⟨h₁, h₂⟩ => Nat.lt_of_le_of_ne h₁ fun e => h₂ ?_
  simp only [Array.mem_toList_iff] at ha hb
  obtain ⟨ta, hta, hca⟩ := mem_flatPairs.mp (hg.mem_flat ha)
  obtain ⟨tb, htb, hcb⟩ := mem_flatPairs.mp (hg.mem_flat hb)
  obtain ⟨-, rfl⟩ := Prod.mk.inj (eq_of_pairwise_ne (hord.imp Nat.ne_of_lt)
    (Array.mem_toList_iff.mpr hta) (Array.mem_toList_iff.mpr htb) e)
  exact Prod.ext e (eq_of_pairwise_ne (hwf _ hta).1.distinct (Array.mem_toList_iff.mpr hca)
    (Array.mem_toList_iff.mpr hcb) ((hkeys a ha).2.trans (hkeys b hb).2.symm))

theorem collectDupsAux_sound (trees : Array (Nat × ConstTrie α)) (covered : Array UInt64) (K : Name)
    (cands : Array (Nat × ConstTrie α)) (acc : Array (Duplicate α))
    (hwf : ∀ p ∈ cands, WF p.2 ∧ p.2.key = K)
    (hsub : ∀ p ∈ cands, ∃ t, (p.1, t) ∈ trees ∧ ∀ n v, Has p.2 n v → Has t n v)
    (hord : cands.toList.Pairwise (fun a b => a.1 < b.1))
    (hacc : ∀ d ∈ acc, Sound trees d) :
    ∀ d ∈ collectDupsAux covered K cands acc, Sound trees d := by
  rw [collectDupsAux_eq]
  split
  · exact hacc
  · refine foldChildGroups_inv _ (fun s => ∀ d ∈ s, Sound trees d) ?_ (fun _ _ _ h => h) ?_
    · split
      · rename_i h2
        intro d hd
        rcases Array.mem_push.mp hd with hd | rfl
        · exact hacc d hd
        · refine ⟨by simp only; omega, fun e he => ?_, ?_⟩
          · obtain ⟨p, hp, hpe⟩ := Array.mem_filterMap.mp he
            obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp hpe
            obtain ⟨t, ht, hst⟩ := hsub p hp
            exact ⟨t, ht, hst _ _ ((hwf p hp).2 ▸ Has.here hv)⟩
          · rw [Array.toList_filterMap, List.pairwise_filterMap]
            refine hord.imp fun h x hx y hy => ?_
            obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hx
            obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hy
            exact h
      · exact hacc
    · intro s g h₁ h₂ hs hg
      refine collectDupsAux_sound trees covered _ g s (hg.wf h₁ hwf) (fun z hz => ?_)
        (hg.ordered h₁ hwf hord) hs
      obtain ⟨t, ht, hc⟩ := mem_flatPairs.mp (hg.mem_flat hz)
      obtain ⟨T, hT, hsT⟩ := hsub _ ht
      exact ⟨T, hT, fun n v h => hsT n v (Has.child hc h)⟩
termination_by maxSize cands
decreasing_by exact maxSize_lt h₁ h₂

/--
Completeness: a name declared by two modules is reported unless a bit is set in both modules'
`covered` masks, meaning some direct import's compilation loaded both and already checked the pair.
-/
theorem collectDuplicates_complete (trees : Array (Nat × ConstTrie α)) (covered : Array UInt64)
    (hwf : ∀ p ∈ trees, WF p.2 ∧ p.2.key = .anonymous)
    (hi : (i, ti) ∈ trees) (hj : (j, tj) ∈ trees) (hij : i ≠ j)
    (hvi : Has ti n vi) (hvj : Has tj n vj)
    (hcov : covered.isEmpty ∨ covered[i]! &&& covered[j]! = 0) :
    ∃ d ∈ collectDuplicates trees covered,
      d.name = n ∧ (vi, i) ∈ d.entries ∧ (vj, j) ∈ d.entries := by
  have := two_le_size_of_mem hi hj (by simp [hij])
  rw [collectDuplicates, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  exact collectDupsAux_complete covered _ trees #[] hwf hi hj hij hvi hvj hcov

/-- Soundness: every reported duplicate has at least two entries, all genuine, in module order. -/
theorem collectDuplicates_sound (trees : Array (Nat × ConstTrie α)) (covered : Array UInt64)
    (hwf : ∀ p ∈ trees, WF p.2 ∧ p.2.key = .anonymous)
    (hord : trees.toList.Pairwise (fun a b => a.1 < b.1)) :
    ∀ d ∈ collectDuplicates trees covered, Sound trees d := by
  rw [collectDuplicates]
  split
  · simp
  · exact collectDupsAux_sound trees covered _ trees #[] hwf
      (fun p hp => ⟨p.2, hp, fun _ _ h => h⟩) hord (by simp)

end ConstTrieDupSpec
