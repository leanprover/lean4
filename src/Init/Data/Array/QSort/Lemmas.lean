/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Init.Data.Array.QSort.Basic
public import Init.Data.Array.Perm
import all Init.Data.Array.QSort.Basic
import Init.Data.Vector.Lemmas
import Init.Data.Vector.Perm
import Init.Omega
import Init.TacticsExtra

public section

set_option linter.listVariables true

namespace Array

open Vector

private theorem qpartition_eqLoop_perm (cmp : α → α → Ordering) (lo hi : Nat) (hhi : hi < n)
    (pivot : α) (as : Vector α n) (i k j : Nat) (ilo : lo ≤ i) (ik : i ≤ k)
    (kj : k ≤ j) (jhi : j ≤ hi) :
    (qpartition.eqLoop cmp lo hi hhi pivot as i k j ilo ik kj jhi).2 ~ as := by
  fun_induction qpartition.eqLoop
  case case1 =>
    apply Vector.Perm.trans
    · assumption
    · apply Vector.swap_perm <;> omega
  case case2 => assumption
  case case3 =>
    apply Vector.Perm.trans
    · assumption
    · apply Vector.swap_perm <;> omega
  case case4 => apply Vector.swap_perm <;> omega

private theorem qpartition_loop_perm (cmp : α → α → Ordering) (lo hi : Nat) (hhi : hi < n)
    (pivot : α) (as : Vector α n) (i k : Nat) (ilo : lo ≤ i) (ik : i ≤ k) (khi : k ≤ hi) :
    (qpartition.loop cmp lo hi hhi pivot as i k ilo ik khi).2 ~ as := by
  fun_induction qpartition.loop
  case case1 =>
    apply Vector.Perm.trans
    · assumption
    · apply Vector.swap_perm <;> omega
  case case2 => assumption
  case case3 =>
    apply Vector.Perm.trans
    · apply qpartition_eqLoop_perm
    · apply Vector.swap_perm <;> omega
  case case4 => apply Vector.swap_perm <;> omega

private theorem qpartition_perm (as : Vector α n) (cmp : α → α → Ordering) (lo hi : Nat)
    (w : lo ≤ hi) (hlo : lo < n) (hhi : hi < n) :
    (qpartition as cmp lo hi w hlo hhi).2 ~ as := by
  unfold qpartition
  apply Vector.Perm.trans
  · apply qpartition_loop_perm
  repeat' first
    | split
    | apply Vector.Perm.trans
      · apply Vector.swap_perm <;> omega
    | exact Vector.Perm.rfl

private theorem qsortBy_sort_perm (as : Vector α n) (cmp : α → α → Ordering)
    (lo hi : Nat) (w : lo ≤ hi) (hhi : hi ≤ n) :
    qsortBy.sort cmp as lo hi w hhi ~ as := by
  fun_induction qsortBy.sort
  case case1 =>
    rename_i xs lo₀ hi₀ w₀ hhi₀ h mid₁ mid₂ hmids ys hpart ih₃ ih₂ ih₁
    apply Vector.Perm.trans ih₁
    apply Vector.Perm.trans ih₂
    have hp := qpartition_perm xs cmp lo₀ (hi₀ - 1) (by omega) (by omega) (by omega)
    simpa only [hpart] using hp
  case case2 => exact Vector.Perm.rfl

private theorem qsortBy_perm (as : Array α) (cmp : α → α → Ordering) (lo hi : Nat) :
    qsortBy as cmp lo hi ~ as := by
  unfold qsortBy
  split
  · exact Array.Perm.rfl
  · exact (qsortBy_sort_perm ..).toArray

private theorem getElem_qpartition_eqLoop_of_not_mem (cmp : α → α → Ordering)
    (lo hi : Nat) (hhi : hi < n) (pivot : α) (as : Vector α n) (i k j : Nat)
    (ilo : lo ≤ i) (ik : i ≤ k) (kj : k ≤ j) (jhi : j ≤ hi)
    (l : Nat) (hl : l < n) (hout : l < lo ∨ hi < l) :
    (qpartition.eqLoop cmp lo hi hhi pivot as i k j ilo ik kj jhi).2[l] = as[l] := by
  fun_induction qpartition.eqLoop
  case case1 =>
    rename_i xs i₀ k₀ j₀ _ _ _ _ _ _ ih
    calc
      _ = (xs.swap i₀ k₀ (by omega) (by omega))[l] := ih
      _ = xs[l] := by apply Vector.getElem_swap_of_ne <;> omega
  case case2 => assumption
  case case3 =>
    rename_i xs i₀ k₀ j₀ _ _ _ _ _ _ ih
    calc
      _ = (xs.swap k₀ (j₀ - 1) (by omega) (by omega))[l] := ih
      _ = xs[l] := by apply Vector.getElem_swap_of_ne <;> omega
  case case4 =>
    apply Vector.getElem_swap_of_ne <;> omega

private theorem getElem_qpartition_loop_of_not_mem (cmp : α → α → Ordering)
    (lo hi : Nat) (hhi : hi < n) (pivot : α) (as : Vector α n) (i k : Nat)
    (ilo : lo ≤ i) (ik : i ≤ k) (khi : k ≤ hi)
    (l : Nat) (hl : l < n) (hout : l < lo ∨ hi < l) :
    (qpartition.loop cmp lo hi hhi pivot as i k ilo ik khi).2[l] = as[l] := by
  fun_induction qpartition.loop
  case case1 =>
    rename_i xs i₀ k₀ _ _ _ _ _ ih
    calc
      _ = (xs.swap i₀ k₀ (by omega) (by omega))[l] := ih
      _ = xs[l] := by apply Vector.getElem_swap_of_ne <;> omega
  case case2 => assumption
  case case3 =>
    rename_i xs i₀ k₀ _ _ _ _ _
    calc
      _ = (xs.swap i₀ k₀ (by omega) (by omega))[l] := by
        apply getElem_qpartition_eqLoop_of_not_mem <;> omega
      _ = xs[l] := by apply Vector.getElem_swap_of_ne <;> omega
  case case4 => apply Vector.getElem_swap_of_ne <;> omega

private theorem getElem_qpartition_of_not_mem (as : Vector α n) (cmp : α → α → Ordering)
    (lo hi : Nat) (w : lo ≤ hi) (hlo : lo < n) (hhi : hi < n) (l : Nat) (hl : l < n)
    (hout : l < lo ∨ hi < l) :
    (qpartition as cmp lo hi w hlo hhi).2[l] = as[l] := by
  unfold qpartition
  rw [getElem_qpartition_loop_of_not_mem]
  repeat' first
    | split
    | rw [Vector.getElem_swap_of_ne (by omega) (by omega)]
  all_goals first | rfl | assumption

private theorem getElem_qsortBy_sort_of_not_mem (as : Vector α n) (cmp : α → α → Ordering)
    (lo hi : Nat) (w : lo ≤ hi) (hhi : hi ≤ n) (l : Nat) (hl : l < n)
    (hout : l < lo ∨ hi ≤ l) :
    (qsortBy.sort cmp as lo hi w hhi)[l] = as[l] := by
  fun_induction qsortBy.sort
  case case1 =>
    rename_i xs lo₀ hi₀ w₀ hhi₀ h mid₁ mid₂ hmids xs₁ hpart ih₃ ih₂ ih₁
    rw [ih₁ (by omega), ih₂ (by omega)]
    have hp := getElem_qpartition_of_not_mem xs cmp lo₀ (hi₀ - 1) (by omega)
      (by omega) (by omega) l hl (by omega)
    simpa only [hpart] using hp
  case case2 => rfl

private theorem qpartition_eqLoop_classifies (cmp : α → α → Ordering)
    (lo hi : Nat) (hhi : hi < n) (pivot : α) (as : Vector α n) (i k j : Nat)
    (ilo : lo ≤ i) (ik : i ≤ k) (kj : k ≤ j) (jhi : j ≤ hi)
    (lower : ∀ l, (hl : l < n) → lo ≤ l → l < i → cmp as[l] pivot = .lt)
    (middle : ∀ l, (hl : l < n) → i ≤ l → l < k → cmp as[l] pivot = .eq)
    (upper : ∀ l, (hl : l < n) → j ≤ l → l < hi → cmp as[l] pivot = .gt)
    (atHi : as[hi] = pivot)
    (self : cmp pivot pivot = .eq) :
    let r := qpartition.eqLoop cmp lo hi hhi pivot as i k j ilo ik kj jhi
    (∀ l, (hl : l < n) → lo ≤ l → l < r.1.1.1 → cmp r.2[l] pivot = .lt) ∧
    (∀ l, (hl : l < n) → r.1.1.1 ≤ l → l < r.1.1.2 → cmp r.2[l] pivot = .eq) ∧
    (∀ l, (hl : l < n) → r.1.1.2 ≤ l → l ≤ hi → cmp r.2[l] pivot = .gt) := by
  fun_induction qpartition.eqLoop
  case case1 =>
    rename_i xs i₀ k₀ j₀ ilo₀ ik₀ kj₀ jhi₀ hk x ih
    apply ih
    · intro l hl h₁ h₂
      rw [Vector.getElem_swap]
      split <;> rename_i h
      · subst l; simpa using x
      split <;> rename_i h'
      · omega
      · apply lower <;> omega
    · intro l hl h₁ h₂
      rw [Vector.getElem_swap]
      split <;> rename_i h
      · omega
      split <;> rename_i h'
      · subst l
        apply middle <;> omega
      · apply middle <;> omega
    · intro l hl h₁ h₂
      rw [Vector.getElem_swap_of_ne (by omega) (by omega)]
      apply upper <;> omega
    · rw [Vector.getElem_swap_of_ne (by omega) (by omega)]
      exact atHi
  case case2 =>
    rename_i xs i₀ k₀ j₀ ilo₀ ik₀ kj₀ jhi₀ hk x ih
    apply ih
    · exact lower
    · intro l hl h₁ h₂
      if h : l = k₀ then
        subst l
        simpa using x
      else
        apply middle <;> omega
    · intro l hl h₁ h₂
      apply upper <;> assumption
    · exact atHi
  case case3 =>
    rename_i xs i₀ k₀ j₀ ilo₀ ik₀ kj₀ jhi₀ hk x ih
    apply ih
    · intro l hl h₁ h₂
      rw [Vector.getElem_swap_of_ne (by omega) (by omega)]
      apply lower <;> omega
    · intro l hl h₁ h₂
      rw [Vector.getElem_swap_of_ne (by omega) (by omega)]
      apply middle <;> omega
    · intro l hl h₁ h₂
      if h : l = j₀ - 1 then
        subst l
        rw [Vector.getElem_swap_right]
        simpa using x
      else
        rw [Vector.getElem_swap_of_ne (by omega) h]
        apply upper <;> omega
    · rw [Vector.getElem_swap_of_ne (by omega) (by omega)]
      exact atHi
  case case4 =>
    rename_i xs i₀ k₀ j₀ ilo₀ ik₀ kj₀ jhi₀ hk
    simp only
    constructor
    · intro l hl h₁ h₂
      rw [Vector.getElem_swap_of_ne (by omega) (by omega)]
      apply lower <;> omega
    constructor
    · intro l hl h₁ h₂
      if h : l = j₀ then
        subst l
        simpa [atHi] using self
      else
        rw [Vector.getElem_swap_of_ne h (by omega)]
        apply middle <;> omega
    · intro l hl h₁ h₂
      if h : l = hi then
        subst l
        simpa using upper j₀ (by omega) (by omega) (by omega)
      else
        rw [Vector.getElem_swap_of_ne (by omega) h]
        apply upper <;> omega

private theorem qpartition_loop_classifies (cmp : α → α → Ordering)
    (lo hi : Nat) (hhi : hi < n) (pivot : α) (as : Vector α n) (i k : Nat)
    (ilo : lo ≤ i) (ik : i ≤ k) (khi : k ≤ hi)
    (lower : ∀ l, (hl : l < n) → lo ≤ l → l < i → cmp as[l] pivot = .lt)
    (upper : ∀ l, (hl : l < n) → i ≤ l → l < k → cmp as[l] pivot = .gt)
    (atHi : as[hi] = pivot)
    (self : cmp pivot pivot = .eq) :
    let r := qpartition.loop cmp lo hi hhi pivot as i k ilo ik khi
    (∀ l, (hl : l < n) → lo ≤ l → l < r.1.1.1 → cmp r.2[l] pivot = .lt) ∧
    (∀ l, (hl : l < n) → r.1.1.1 ≤ l → l < r.1.1.2 → cmp r.2[l] pivot = .eq) ∧
    (∀ l, (hl : l < n) → r.1.1.2 ≤ l → l ≤ hi → cmp r.2[l] pivot = .gt) := by
  fun_induction qpartition.loop
  case case1 =>
    rename_i xs i₀ k₀ ilo₀ ik₀ khi₀ hk x ih
    apply ih
    · intro l hl h₁ h₂
      rw [Vector.getElem_swap]
      split <;> rename_i h
      · subst l; simpa using x
      split <;> rename_i h'
      · omega
      · apply lower <;> omega
    · intro l hl h₁ h₂
      rw [Vector.getElem_swap]
      split <;> rename_i h
      · omega
      split <;> rename_i h'
      · subst l
        apply upper <;> omega
      · apply upper <;> omega
    · rw [Vector.getElem_swap_of_ne (by omega) (by omega)]
      exact atHi
  case case2 =>
    rename_i xs i₀ k₀ ilo₀ ik₀ khi₀ hk x ih
    apply ih
    · exact lower
    · intro l hl h₁ h₂
      if h : l = k₀ then
        subst l
        simpa using x
      else
        apply upper <;> omega
    · exact atHi
  case case3 =>
    rename_i xs i₀ k₀ ilo₀ ik₀ khi₀ hk x
    apply qpartition_eqLoop_classifies
    · intro l hl h₁ h₂
      rw [Vector.getElem_swap_of_ne (by omega) (by omega)]
      apply lower <;> omega
    · intro l hl h₁ h₂
      have hli : l = i₀ := by omega
      subst l
      rw [Vector.getElem_swap_left]
      simpa using x
    · intro l hl h₁ h₂
      omega
    · rw [Vector.getElem_swap_of_ne (by omega) (by omega)]
      exact atHi
    · exact self
  case case4 =>
    rename_i xs i₀ k₀ ilo₀ ik₀ khi₀ hk
    simp only
    constructor
    · intro l hl h₁ h₂
      rw [Vector.getElem_swap_of_ne (by omega) (by omega)]
      apply lower <;> omega
    constructor
    · intro l hl h₁ h₂
      have hli : l = i₀ := by omega
      subst l
      rw [Vector.getElem_swap_left]
      simpa [atHi] using self
    · intro l hl h₁ h₂
      if h : l = hi then
        subst l
        rw [Vector.getElem_swap_right]
        apply upper <;> omega
      else
        rw [Vector.getElem_swap_of_ne (by omega) h]
        apply upper <;> omega

private theorem qpartition_classifies (as : Vector α n) (cmp : α → α → Ordering)
    (self : ∀ a, cmp a a = .eq) (lo hi : Nat) (w : lo ≤ hi) (hlo : lo < n) (hhi : hi < n) :
    let r := qpartition as cmp lo hi w hlo hhi
    ∃ pivot,
      (∀ l, (hl : l < n) → lo ≤ l → l < r.1.1.1 → cmp r.2[l] pivot = .lt) ∧
      (∀ l, (hl : l < n) → r.1.1.1 ≤ l → l < r.1.1.2 → cmp r.2[l] pivot = .eq) ∧
      (∀ l, (hl : l < n) → r.1.1.2 ≤ l → l ≤ hi → cmp r.2[l] pivot = .gt) := by
  unfold qpartition
  simp only
  refine ⟨_, qpartition_loop_classifies cmp lo hi hhi _ _ lo lo ?_ ?_ ?_ ?_ ?_ rfl ?_⟩
  · omega
  · omega
  · omega
  · omega
  · intro; omega
  · apply self

private theorem holds_swap (p : α → Prop) (as : Vector α n) (lo hi i j : Nat)
    (hi' : i < n) (hj' : j < n) (hilo : lo ≤ i) (hihi : i ≤ hi)
    (hjlo : lo ≤ j) (hjhi : j ≤ hi)
    (h : ∀ l, (hl : l < n) → lo ≤ l → l ≤ hi → p as[l]) :
    ∀ l, (hl : l < n) → lo ≤ l → l ≤ hi → p (as.swap i j hi' hj')[l] := by
  intro l hl hlo hhi
  rw [Vector.getElem_swap]
  split <;> rename_i heq
  · apply h <;> omega
  split <;> rename_i heq'
  · apply h <;> omega
  · apply h <;> omega

private theorem qpartition_eqLoop_holds (p : α → Prop) (cmp : α → α → Ordering)
    (lo hi : Nat) (hhi : hi < n) (pivot : α) (as : Vector α n) (i k j : Nat)
    (ilo : lo ≤ i) (ik : i ≤ k) (kj : k ≤ j) (jhi : j ≤ hi)
    (h : ∀ l, (hl : l < n) → lo ≤ l → l ≤ hi → p as[l]) :
    ∀ l, (hl : l < n) → lo ≤ l → l ≤ hi →
      p (qpartition.eqLoop cmp lo hi hhi pivot as i k j ilo ik kj jhi).2[l] := by
  fun_induction qpartition.eqLoop
  case case1 =>
    apply_assumption
    exact holds_swap p _ lo hi _ _ _ _ (by omega) (by omega) (by omega) (by omega) h
  case case2 => apply_assumption; exact h
  case case3 =>
    apply_assumption
    exact holds_swap p _ lo hi _ _ _ _ (by omega) (by omega) (by omega) (by omega) h
  case case4 =>
    exact holds_swap p _ lo hi _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) h

private theorem qpartition_loop_holds (p : α → Prop) (cmp : α → α → Ordering)
    (lo hi : Nat) (hhi : hi < n) (pivot : α) (as : Vector α n) (i k : Nat)
    (ilo : lo ≤ i) (ik : i ≤ k) (khi : k ≤ hi)
    (h : ∀ l, (hl : l < n) → lo ≤ l → l ≤ hi → p as[l]) :
    ∀ l, (hl : l < n) → lo ≤ l → l ≤ hi →
      p (qpartition.loop cmp lo hi hhi pivot as i k ilo ik khi).2[l] := by
  fun_induction qpartition.loop
  case case1 =>
    apply_assumption
    exact holds_swap p _ lo hi _ _ _ _ (by omega) (by omega) (by omega) (by omega) h
  case case2 => apply_assumption; exact h
  case case3 =>
    apply qpartition_eqLoop_holds
    exact holds_swap p _ lo hi _ _ _ _ (by omega) (by omega) (by omega) (by omega) h
  case case4 =>
    exact holds_swap p _ lo hi _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) h

private theorem qpartition_holds (p : α → Prop) (as : Vector α n)
    (cmp : α → α → Ordering) (lo hi : Nat) (w : lo ≤ hi) (hlo : lo < n) (hhi : hi < n)
    (h : ∀ l, (hl : l < n) → lo ≤ l → l ≤ hi → p as[l]) :
    ∀ l, (hl : l < n) → lo ≤ l → l ≤ hi → p (qpartition as cmp lo hi w hlo hhi).2[l] := by
  unfold qpartition
  apply qpartition_loop_holds
  repeat' first
    | split
    | apply holds_swap p _ lo hi <;> try omega
  exact h

private theorem qsortBy_sort_holds (p : α → Prop) (as : Vector α n)
    (cmp : α → α → Ordering) (lo hi : Nat) (w : lo ≤ hi) (hhi : hi ≤ n)
    (h : ∀ l, (hl : l < n) → lo ≤ l → l < hi → p as[l]) :
    ∀ l, (hl : l < n) → lo ≤ l → l < hi → p (qsortBy.sort cmp as lo hi w hhi)[l] := by
  fun_induction qsortBy.sort
  case case1 =>
    rename_i xs lo₀ hi₀ w₀ hhi₀ hlong mid₁ mid₂ hmids xs₁ hpart ih₃ ih₂ ih₁
    have hp₀ := qpartition_holds p xs cmp lo₀ (hi₀ - 1) (by omega) (by omega) (by omega)
      (fun l hl h₁ h₂ => h l hl h₁ (by omega))
    have hp : ∀ l, (hl : l < n) → lo₀ ≤ l → l < hi₀ → p xs₁[l] := by
      simpa only [hpart] using fun l hl h₁ h₂ => hp₀ l hl h₁ (by omega)
    intro l hl h₁ h₂
    if hleft : l < mid₁ then
      rw [getElem_qsortBy_sort_of_not_mem (l := l) (hout := by omega)]
      exact ih₂ (fun l hl h₁ h₂ => hp l hl h₁ (by omega)) l hl (by omega) hleft
    else if hmiddle : l < mid₂ then
      rw [getElem_qsortBy_sort_of_not_mem (l := l) (hout := by omega)]
      rw [getElem_qsortBy_sort_of_not_mem (l := l) (hout := by omega)]
      exact hp l hl (by omega) (by omega)
    else
      apply ih₁
      · intro l hl h₁ h₂
        rw [getElem_qsortBy_sort_of_not_mem (l := l) (hout := by omega)]
        exact hp l hl (by omega) (by omega)
      · omega
      · assumption
  case case2 => exact h

private theorem not_lt_p_of_compareOfLess_ne_gt (lt : α → α → Bool)
    (lt_asymm : ∀ {a b}, lt a b → ¬ lt b a) {a pivot : α}
    (h : compareOfLess lt a pivot ≠ .gt) : ¬ lt pivot a := by
  if hap : lt a pivot then
    exact lt_asymm hap
  else if hpa : lt pivot a then
    simp [compareOfLess, hap, hpa] at h
  else
    exact hpa

private theorem not_lt_p_of_compareOfLess_ne_lt (lt : α → α → Bool)
    {a pivot : α} (h : compareOfLess lt a pivot ≠ .lt) : ¬ lt a pivot := by
  if hap : lt a pivot then
    simp [compareOfLess, hap] at h
  else
    exact hap

private theorem not_lt_of_ordered_partition_classes (lt : α → α → Bool)
    (lt_asymm : ∀ {a b}, lt a b → ¬ lt b a)
    (le_trans : ∀ {a b c}, ¬ lt b a → ¬ lt c b → ¬ lt c a)
    {a b pivot : α} (ha : compareOfLess lt a pivot ≠ .gt)
    (hb : compareOfLess lt b pivot ≠ .lt) : ¬ lt b a :=
  le_trans (not_lt_p_of_compareOfLess_ne_gt lt lt_asymm ha)
    (not_lt_p_of_compareOfLess_ne_lt lt hb)

private theorem qsortBy_sort_sorted (lt : α → α → Bool)
    (lt_asymm : ∀ {a b}, lt a b → ¬ lt b a)
    (le_trans : ∀ {a b c}, ¬ lt b a → ¬ lt c b → ¬ lt c a)
    (as : Vector α n) (lo hi : Nat) (w : lo ≤ hi) (hhi : hi ≤ n) :
    ∀ i j, (hi' : i < n) → (hj' : j < n) → lo ≤ i → i < j → j < hi →
      ¬ lt (qsortBy.sort (compareOfLess lt) as lo hi w hhi)[j]
        (qsortBy.sort (compareOfLess lt) as lo hi w hhi)[i] := by
  fun_induction qsortBy.sort
  case case1 =>
    rename_i xs lo₀ hi₀ w₀ hhi₀ hlong mid₁ mid₂ hmids xs₁ hpart ih₃ ih₂ ih₁
    have hc₀ := qpartition_classifies xs (compareOfLess lt) (fun a => by
      have haa : ¬ lt a a := fun h => lt_asymm h h
      simp [compareOfLess, haa])
      lo₀ (hi₀ - 1) (by omega) (by omega) (by omega)
    simp only [hpart] at hc₀
    obtain ⟨pivot, hlower₀, hmiddle₀, hupper₀⟩ := hc₀
    have hlower : ∀ l, (hl : l < n) → lo₀ ≤ l → l < mid₁ →
        compareOfLess lt (qsortBy.sort (compareOfLess lt)
          (qsortBy.sort (compareOfLess lt) xs₁ lo₀ mid₁) mid₂ hi₀)[l] pivot = .lt := by
      intro l hl h₁ h₂
      rw [getElem_qsortBy_sort_of_not_mem (l := l) (hout := by omega)]
      exact qsortBy_sort_holds (fun a => compareOfLess lt a pivot = .lt) xs₁
        (compareOfLess lt) lo₀ mid₁ (by omega) (by omega)
        (fun l hl h₁ h₂ => hlower₀ l hl h₁ h₂) l hl h₁ h₂
    have hmiddle : ∀ l, (hl : l < n) → mid₁ ≤ l → l < mid₂ →
        compareOfLess lt (qsortBy.sort (compareOfLess lt)
          (qsortBy.sort (compareOfLess lt) xs₁ lo₀ mid₁) mid₂ hi₀)[l] pivot = .eq := by
      intro l hl h₁ h₂
      rw [getElem_qsortBy_sort_of_not_mem (l := l) (hout := by omega)]
      rw [getElem_qsortBy_sort_of_not_mem (l := l) (hout := by omega)]
      exact hmiddle₀ l hl h₁ h₂
    have hupper : ∀ l, (hl : l < n) → mid₂ ≤ l → l < hi₀ →
        compareOfLess lt (qsortBy.sort (compareOfLess lt)
          (qsortBy.sort (compareOfLess lt) xs₁ lo₀ mid₁) mid₂ hi₀)[l] pivot = .gt := by
      apply qsortBy_sort_holds (fun a => compareOfLess lt a pivot = .gt)
        (qsortBy.sort (compareOfLess lt) xs₁ lo₀ mid₁) (compareOfLess lt)
        mid₂ hi₀ (by omega) (by omega)
      intro l hl h₁ h₂
      rw [getElem_qsortBy_sort_of_not_mem (l := l) (hout := by omega)]
      exact hupper₀ l hl h₁ (by omega)
    intro i j hi' hj' hloi hij hjhi
    if hjleft : j < mid₁ then
      rw [getElem_qsortBy_sort_of_not_mem (l := j) (hout := by omega)]
      rw [getElem_qsortBy_sort_of_not_mem (l := i) (hout := by omega)]
      exact ih₂ i j hi' hj' hloi hij hjleft
    else if hiright : mid₂ ≤ i then
      exact ih₁ i j hi' hj' hiright hij hjhi
    else
      refine not_lt_of_ordered_partition_classes lt lt_asymm le_trans (pivot := pivot) ?_ ?_
      · if h : i < mid₁ then
          simp [hlower i hi' hloi h]
        else
          simp [hmiddle i hi' (by omega) (by omega)]
      · if h : j < mid₂ then
          simp [hmiddle j hj' (by omega) h]
        else
          simp [hupper j hj' (by omega) hjhi]
  case case2 => intro; omega

@[simp] theorem size_qsort (as : Array α) (lt : α → α → Bool) (lo hi : Nat) :
    (qsort as lt lo hi).size = as.size :=
  (qsortBy_perm as (compareOfLess lt) lo hi).size_eq

/-- `Array.qsort` does not modify elements outside the inclusive interval from `lo` to `hi`. -/
@[simp] theorem getElem_qsort_of_not_mem (as : Array α) (lt : α → α → Bool)
    (lo hi i : Nat) (hi' : i < as.size) (hout : i < lo ∨ hi < i) :
    getElem (qsort as lt lo hi) i (by simpa using hi') = as[i] := by
  unfold qsort qsortBy
  split <;> rename_i hsize
  · omega
  · rw [Vector.getElem_toArray]
    if hout' :
        i < min lo (as.size - 1) ∨ max (min lo (as.size - 1)) (min hi (as.size - 1)) < i then
    · apply getElem_qsortBy_sort_of_not_mem
      omega
    else
      have hlo : min lo (as.size - 1) = i := by omega
      have hhi : max i (min hi (as.size - 1)) = i := by omega
      simp only [hlo, hhi]
      unfold qsortBy.sort
      simp

theorem qsort_perm (as : Array α) (lt : α → α → Bool) (lo hi : Nat) :
    qsort as lt lo hi ~ as :=
  qsortBy_perm as (compareOfLess lt) lo hi

@[simp] theorem mem_qsort {a : α} (as : Array α) (lt : α → α → Bool) (lo hi : Nat) :
    a ∈ qsort as lt lo hi ↔ a ∈ as :=
  (qsort_perm as lt lo hi).mem_iff

/-- The slice sorted by `Array.qsort` is ordered at every pair of indices. -/
theorem qsort_sorted' (lt : α → α → Bool)
    (lt_asymm : ∀ {a b}, lt a b → ¬ lt b a)
    (le_trans : ∀ {a b c}, ¬ lt b a → ¬ lt c b → ¬ lt c a)
    (as : Array α) (lo hi i j : Nat) (hlo : lo ≤ i) (hij : i < j) (hhi : j ≤ hi)
    (hj : j < as.size) :
    ¬ lt (getElem (as.qsort lt lo hi) j (by simpa using hj))
      (getElem (as.qsort lt lo hi) i (by simp; omega)) := by
  unfold qsort qsortBy
  split <;> rename_i hsize
  · omega
  · apply qsortBy_sort_sorted lt lt_asymm le_trans <;> omega

/-- `Array.qsort` returns an array ordered at every pair of indices. -/
theorem qsort_sorted (lt : α → α → Bool)
    (lt_asymm : ∀ {a b}, lt a b → ¬ lt b a)
    (le_trans : ∀ {a b c}, ¬ lt b a → ¬ lt c b → ¬ lt c a)
    (as : Array α) (i j : Nat) (hij : i < j) (hj : j < (qsort as lt).size) :
    ¬ lt (as.qsort lt)[j] (as.qsort lt)[i] := by
  have hj' : j < as.size := by simpa using hj
  exact qsort_sorted' lt lt_asymm le_trans as 0 (as.size - 1) i j
    (by omega) hij (by omega) hj'

/-- The slice sorted by `Array.qsort` is ordered at adjacent indices. -/
theorem qsort_sorted₁' (lt : α → α → Bool)
    (lt_asymm : ∀ {a b}, lt a b → ¬ lt b a)
    (le_trans : ∀ {a b c}, ¬ lt b a → ¬ lt c b → ¬ lt c a)
    (as : Array α) (lo hi i : Nat) (hlo : lo ≤ i) (hhi : i < hi) (hi' : i + 1 < as.size) :
    ¬ lt (getElem (as.qsort lt lo hi) (i + 1) (by simpa using hi'))
      (getElem (as.qsort lt lo hi) i (by simp; omega)) :=
  qsort_sorted' lt lt_asymm le_trans as lo hi i (i + 1) hlo (by omega) (by omega) hi'

/-- `Array.qsort` returns an array ordered at adjacent indices. -/
theorem qsort_sorted₁ (lt : α → α → Bool)
    (lt_asymm : ∀ {a b}, lt a b → ¬ lt b a)
    (le_trans : ∀ {a b c}, ¬ lt b a → ¬ lt c b → ¬ lt c a)
    (as : Array α) (i : Nat) (hi : i + 1 < (qsort as lt).size) :
    ¬ lt (as.qsort lt)[i + 1] (as.qsort lt)[i] :=
  qsort_sorted lt lt_asymm le_trans as i (i + 1) (by omega) hi

end Array
