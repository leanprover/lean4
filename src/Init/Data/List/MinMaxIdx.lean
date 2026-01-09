/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.List.MinMaxOn
import all Init.Data.List.MinMaxOn
import all Init.Data.Order.MinMaxOn
public import Init.Data.List.Pairwise
public import Init.Data.Subtype.Order
import Init.Data.Order.Lemmas
import Init.Data.List.Nat.TakeDrop
import Init.Data.Order.Opposite

public section

open Std

set_option doc.verso true
set_option linter.missingDocs true
set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace List

@[inline]
def minIdxOn [LE β] [DecidableLE β] (f : α → β) (xs : List α) (h : xs ≠ []) : Nat :=
  match xs with
  | y :: ys => go y 0 1 ys
where
  @[specialize]
  go (x : α) (i : Nat) (j : Nat) (xs : List α) :=
    match xs with
    | [] => i
    | y :: ys =>
        if f x ≤ f y then
          go x i (j + 1) ys
        else
          go y j (j + 1) ys

@[inline]
def minIdxOn? [LE β] [DecidableLE β] (f : α → β) (xs : List α) : Option Nat :=
  match xs with
  | [] => none
  | y :: ys => some ((y :: ys).minIdxOn f (nomatch ·))

@[inline]
def maxIdxOn [LE β] [DecidableLE β] (f : α → β) (xs : List α) (h : xs ≠ []) : Nat :=
  letI := (inferInstanceAs (LE β)).opposite
  xs.minIdxOn f h

@[inline]
def maxIdxOn? [LE β] [DecidableLE β] (f : α → β) (xs : List α) : Option Nat :=
  letI := (inferInstanceAs (LE β)).opposite
  xs.minIdxOn? f

private theorem minIdxOn.go_lt_length_add [LE β] [DecidableLE β] {f : α → β} {x : α} {i j : Nat}
    {xs : List α} (h : i < j) :
    List.minIdxOn.go f x i j xs < xs.length + j := by
  induction xs generalizing x i j
  · simp [go, h]
  · rename_i y ys ih
    simp [go, Nat.add_assoc, Nat.add_comm 1]
    split
    · exact ih (Nat.lt_succ_of_lt ‹i < j›)
    · exact ih (Nat.lt_succ_self j)

private theorem minIdxOn.go_eq_of_forall_le [LE β] [DecidableLE β] {f : α → β}
    {x : α} {i j : Nat} {xs : List α} (h : ∀ y ∈ xs, f x ≤ f y) :
    List.minIdxOn.go f x i j xs = i := by
  induction xs generalizing x i j
  · simp [go]
  · rename_i y ys ih
    simp [go]
    split
    · apply ih
      simp_all
    · simp_all

private theorem aux' {xs : List α} {k : Nat} {y : α} {ys : List α} (h : xs.drop k = y :: ys) :
    ∃ hlt : k < xs.length, xs[k] = y := by
  have hlt : k < xs.length := by
    false_or_by_contra
    have : drop k xs = [] := drop_of_length_le (by omega)
    simp [this] at h
  refine ⟨hlt, ?_⟩
  have := take_append_drop k xs
  rw [h] at this
  simp +singlePass only [← this]
  rw [getElem_append_right (length_take_le _ _)]
  simp [length_take_of_le (Nat.le_of_lt hlt)]

private theorem aux {xs : List α} {k : Nat} {y : α} {ys : List α} (h : xs.drop k = y :: ys) :
    xs.take (k + 1) = xs.take k ++ [y] := by
  obtain ⟨hlt, rfl⟩ := aux' h
  rw [take_succ_eq_append_getElem hlt]

private theorem minIdxOn_eq_go_drop [LE β] [DecidableLE β] [IsLinearPreorder β] {f : α → β} {xs : List α} (h : xs ≠ [])
    {k : Nat} :
    ∃ (i : Nat) (hlt : i < xs.length), i ≤ k ∧ xs[i] = (xs.take (k + 1)).minOn f (by simpa) ∧  xs.minIdxOn f h = List.minIdxOn.go f ((xs.take (k + 1)).minOn f (by cases xs <;> simp_all)) i (k + 1) (xs.drop (k + 1)) := by
  match xs with
  | y :: ys =>
    simp only [drop_succ_cons]
    induction k
    · simp [minIdxOn]
    · rename_i k ih
      specialize ih
      obtain ⟨i, hlt, hi, ih⟩ := ih
      simp only [ih, ← drop_drop]
      simp at hlt
      match h : drop k ys with
      | [] =>
        have : ys.length ≤ k := by simp_all
        simp [drop_nil, minIdxOn.go, take_of_length_le, hi, ih, hlt, this, Nat.le_succ_of_le]
      | z :: zs =>
        simp only [minIdxOn.go]
        split
        · have : take (k + 1 + 1) (y :: ys) = take (k + 1) (y :: ys) ++ [z] := by apply aux ‹_›
          simp only [this]
          conv => congr; ext; rhs; rw [List.minOn_append (by simp) (by simp)]
          conv => congr; ext; rhs; ext; rhs; rw [List.minOn_append (by simp) (by simp)]
          simp_all [minOn_eq_left]
          exact ⟨i, Nat.le_succ_of_le ‹i ≤ k›, ⟨by omega, by simp [ih]⟩, rfl⟩
        · have : take (k + 1 + 1) (y :: ys) = take (k + 1) (y :: ys) ++ [z] := by apply aux ‹_›
          simp only [this]
          conv => congr; ext; rhs; rw [List.minOn_append (by simp) (by simp)]
          conv => congr; ext; rhs; ext; rhs; rw [List.minOn_append (by simp) (by simp)]
          simp_all [minOn_eq_right]
          obtain ⟨hlt, rfl⟩ := aux' h
          exact ⟨k + 1, Nat.le_refl _, ⟨by omega, by simp⟩, rfl⟩

theorem minIdxOn_lt_length [LE β] [DecidableLE β] {f : α → β} {xs : List α} (h : xs ≠ []) :
    xs.minIdxOn f h < xs.length := by
  rw [minIdxOn.eq_def]
  split
  simp [minIdxOn.go_lt_length_add]

theorem minIdxOn_le_of_getElem_le [LE β] [DecidableLE β] [IsLinearPreorder β]
    {f : α → β} {xs : List α} (h : xs ≠ [])
    {k : Nat} (hi : k < xs.length) (hle : f xs[k] ≤ f (xs.minOn f h)) :
    xs.minIdxOn f h ≤ k := by
  obtain ⟨i, _, hi, _, h'⟩ := minIdxOn_eq_go_drop (f := f) h (k := k)
  rw [h']
  refine Nat.le_trans ?_ hi
  apply Nat.le_of_eq
  apply minIdxOn.go_eq_of_forall_le
  intro y hy
  refine le_trans (List.apply_minOn_le_of_mem (y := xs[k]) (by rw [mem_take_iff_getElem]; exact ⟨k, by omega, rfl⟩)) ?_
  refine le_trans hle ?_
  apply apply_minOn_le_of_mem
  apply mem_of_mem_drop
  exact hy

theorem getElem_minIdxOn [LE β] [DecidableLE β] [IsLinearPreorder β]
    {f : α → β} {xs : List α} (h : xs ≠ []) :
    haveI := minIdxOn_lt_length (f := f) h
    xs[xs.minIdxOn f h] = xs.minOn f h := by
  obtain ⟨i, hlt, hi, heq, h'⟩ := minIdxOn_eq_go_drop (f := f) h (k := xs.length)
  simp only [drop_eq_nil_of_le (as := xs) (i := xs.length + 1) (by omega), minIdxOn.go] at h'
  simp [h', heq, take_of_length_le (l := xs) (i := xs.length + 1) (by omega)]

theorem minIdxOn_eq_iff [LE β] [DecidableLE β] [IsLinearPreorder β]
    {f : α → β} {xs : List α} (h : xs ≠ []) {i : Nat} :
    xs.minIdxOn f h = i ↔ ∃ hi : i < xs.length, xs[i] = xs.minOn f h ∧
      ∀ (j : Nat) (hj : j < i), ¬ f xs[j] ≤ f (xs.minOn f h) := by
  apply Iff.intro
  · rintro rfl
    refine ⟨List.minIdxOn_lt_length h, List.getElem_minIdxOn h, ?_⟩
    intro j hj hle
    have := minIdxOn_le_of_getElem_le h (k := j) _ hle
    omega
  · rintro ⟨hlt, heq, h'⟩
    specialize h' (xs.minIdxOn f h)
    simp only [getElem_minIdxOn] at h'
    apply le_antisymm
    · apply minIdxOn_le_of_getElem_le h hlt
      rw [heq]
      apply le_refl
    · false_or_by_contra
      apply h' (by omega)
      apply le_refl

@[simp]
theorem minIdxOn_singleton [LE β] [DecidableLE β] {x : α} {f : α → β} :
    [x].minIdxOn f (of_decide_eq_false rfl) = 0 := by
  rw [minIdxOn, minIdxOn.go]

private theorem minIdxOn.go_eq
    [LE β] [DecidableLE β] [IsLinearPreorder β] {x : α} {xs : List α} {f : α → β} :
    List.minIdxOn.go f x i j xs =
      if h : xs = [] then i
      else if f x ≤ f (xs.minOn f h) then i
      else (xs.minIdxOn f h) + j := by
  open scoped Classical.Order in
  induction xs generalizing x i j
  · simp [go]
  · rename_i y ys ih
    simp [go]
    split
    · rw [ih]
      split
      · simp [*]
      · simp [List.minOn_cons, le_apply_minOn_iff, *]
        split
        · rfl
        · rename_i hlt
          simp only [minIdxOn]
          split
          simp [ih]
          rw [if_neg]
          · simp [minIdxOn, Nat.add_assoc, Nat.add_comm 1]
          · simp only [not_le] at hlt ⊢
            exact lt_of_lt_of_le hlt ‹_›
    · rename_i hlt
      rw [if_neg]
      · rw [minIdxOn, ih]
        split
        · simp [*, go]
        · simp [*]
          split
          · simp
          · simp [Nat.add_assoc, Nat.add_comm 1]
      · simp only [not_le] at hlt ⊢
        exact lt_of_le_of_lt (List.apply_minOn_le_of_mem mem_cons_self) hlt

theorem minIdxOn_cons
    [LE β] [DecidableLE β] [IsLinearPreorder β] {x : α} {xs : List α} {f : α → β} :
    (x :: xs).minIdxOn f (by exact of_decide_eq_false rfl) =
      if h : xs = [] then 0
      else if f x ≤ f (xs.minOn f h) then 0
      else (xs.minIdxOn f h) + 1 := by
  simpa [List.minIdxOn] using minIdxOn.go_eq

theorem minIdxOn_eq_zero_iff [LE β] [DecidableLE β] [Std.IsLinearPreorder β]
    {xs : List α} {f : α → β} (h : xs ≠ []) :
    xs.minIdxOn f h = 0 ↔ ∀ x ∈ xs, f (xs.head h) ≤ f x := by
  rw [minIdxOn.eq_def]
  split
  rename_i y ys _
  simp [mem_cons, head_cons, forall_eq_or_imp, le_refl]
  apply Iff.intro
  · intro h
    cases ys
    · simp
    · intro a ha
      refine le_trans ?_ (apply_minOn_le_of_mem ha)
      simpa [minIdxOn.go_eq] using h
  · intro h
    cases ys
    · simp [minIdxOn.go]
    · simpa [minIdxOn.go_eq, List.le_apply_minOn_iff] using h

private def combineMinIdx [LE β] [DecidableLE β]
    (f : α → β) {xs ys : List α} (i j : Nat) (hi : i < xs.length) (hj : j < ys.length) : Nat :=
  if f xs[i] ≤ f ys[j] then
    i
  else
    xs.length + j

private theorem combineMinIdx_lt [LE β] [DecidableLE β]
    (f : α → β) {xs ys : List α} {i j : Nat} (hi : i < xs.length) (hj : j < ys.length) :
    combineMinIdx f i j hi hj < (xs ++ ys).length := by
  simp only [combineMinIdx]
  split <;> (simp; omega)

private theorem combineMinIdx_assoc [LE β] [DecidableLE β] [Std.IsLinearPreorder β]
    {xs ys zs : List α} {i j k : Nat} {f : α → β} (hi : i < xs.length) (hj : j < ys.length) (hk : k < zs.length) :
    combineMinIdx f (combineMinIdx f i j _ _) k
      (combineMinIdx_lt f hi hj) hk = combineMinIdx f i (combineMinIdx f j k _ _) hi (combineMinIdx_lt f hj hk) := by
  open scoped Classical.Order in
  simp only [combineMinIdx]
  split
  · rw [getElem_append_left (by omega)]
    split
    · split
      · rw [getElem_append_left (by omega)]
        simp [*]
      · rw [getElem_append_right (by omega)]
        simp [*]
    · split
      · have := le_trans ‹f xs[i] ≤ f ys[j]› ‹f ys[j] ≤ f zs[k]›
        contradiction
      · rw [getElem_append_right (by omega)]
        simp [*, Nat.add_assoc]
  · rw [getElem_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left]
    split
    · rw [getElem_append_left (by omega), if_neg ‹_›]
    · rename_i h₁ h₂
      simp only [not_le] at h₁ h₂
      rw [getElem_append_right (by omega)]
      simp only [Nat.add_sub_cancel_left]
      have := not_le.mpr <| lt_trans h₂ h₁
      simp [*, Nat.add_assoc]

private theorem minIdxOn_cons_aux [LE β] [DecidableLE β] [Std.IsLinearPreorder β]
    {x : α} {xs : List α} {f : α → β} (hxs : xs ≠ []) :
    (x :: xs).minIdxOn f (by simp) =
      combineMinIdx f _ _ (minIdxOn_lt_length (f := f) (cons_ne_nil x [])) (minIdxOn_lt_length (f := f) hxs) := by
  rw [minIdxOn, combineMinIdx]
  simp [minIdxOn.go_eq, hxs, List.getElem_minIdxOn, Nat.add_comm 1]

private theorem minIdxOn_append_aux [LE β] [DecidableLE β] [Std.IsLinearPreorder β]
    {xs ys : List α} {f : α → β} (hxs : xs ≠ []) (hys : ys ≠ []) :
    (xs ++ ys).minIdxOn f (by simp [hxs]) =
      combineMinIdx f _ _ (minIdxOn_lt_length (f := f) hxs) (minIdxOn_lt_length (f := f) hys) := by
  induction xs
  · contradiction
  · rename_i x xs ih
    match xs with
    | [] => simp [minIdxOn_cons_aux (xs := ys) ‹_›]
    | z :: zs =>
      simp +singlePass only [cons_append]
      simp only [minIdxOn_cons_aux (xs := z :: zs ++ ys) (by simp), ih (by simp),
        minIdxOn_cons_aux (xs := z :: zs) (by simp), combineMinIdx_assoc]

theorem minIdxOn_append [LE β] [DecidableLE β] [Std.IsLinearPreorder β]
    {xs ys : List α} {f : α → β} (hxs : xs ≠ []) (hys : ys ≠ []) :
    (xs ++ ys).minIdxOn f (by simp [hxs]) =
      if f (xs.minOn f hxs) ≤ f (ys.minOn f hys) then
        xs.minIdxOn f hxs
      else
        xs.length + ys.minIdxOn f hys := by
  simp [minIdxOn_append_aux hxs hys, combineMinIdx, getElem_minIdxOn]

theorem left_le_apply_minIdxOn_append [LE β] [DecidableLE β] [Std.IsLinearPreorder β]
    {xs ys : List α} {f : α → β} (h : xs ≠ []) :
    xs.minIdxOn f h ≤ (xs ++ ys).minIdxOn f (by simp [h]) := by
  by_cases hys : ys = []
  · simp [hys]
  · rw [minIdxOn_append h hys]
    split
    · apply Nat.le_refl
    · have := minIdxOn_lt_length (f := f) h
      omega

theorem apply_minIdxOn_take_le [LE β] [DecidableLE β] [Std.IsLinearPreorder β]
    {xs : List α} {f : α → β} {i : Nat} (h : xs.take i ≠ []) :
    (xs.take i).minIdxOn f h ≤ xs.minIdxOn f (List.ne_nil_of_take_ne_nil h) := by
  have := take_append_drop i xs
  conv => rhs; simp +singlePass only [← this]
  apply left_le_apply_minIdxOn_append

@[simp]
theorem minIdxOn_replicate [LE β] [DecidableLE β] [Refl (α := β) (· ≤ ·)]
    {n : Nat} {a : α} {f : α → β} (h : replicate n a ≠ []) :
    (replicate n a).minIdxOn f h = 0 := by
  match n with
  | 0 => simp at h
  | n + 1 =>
    simp [replicate_succ, minIdxOn]
    generalize 1 = j
    induction n generalizing j
    · simp [minIdxOn.go]
    · simp only [replicate_succ, minIdxOn.go] at *
      split
      · simp [*]
      · have := le_refl (f a)
        contradiction

@[simp]
theorem maxIdxOn_singleton [LE β] [DecidableLE β] {x : α} {f : α → β} :
    [x].maxIdxOn f (of_decide_eq_false rfl) = 0 :=
  letI : LE β :=  (inferInstanceAs (LE β)).opposite
  minIdxOn_singleton

theorem maxIdxOn_cons
    [LE β] [DecidableLE β] [IsLinearPreorder β] {x : α} {xs : List α} {f : α → β} :
    (x :: xs).maxIdxOn f (by exact of_decide_eq_false rfl) =
      if h : xs = [] then 0
      else if f (xs.maxOn f h) ≤ f x then 0
      else (xs.maxIdxOn f h) + 1 :=
  letI : LE β :=  (inferInstanceAs (LE β)).opposite
  minIdxOn_cons

theorem maxIdxOn_eq_zero_iff [LE β] [DecidableLE β] [Std.IsLinearPreorder β]
    {xs : List α} {f : α → β} (h : xs ≠ []) :
    xs.maxIdxOn f h = 0 ↔ ∀ x ∈ xs, f x ≤ f (xs.head h) :=
  letI : LE β :=  (inferInstanceAs (LE β)).opposite
  minIdxOn_eq_zero_iff h

theorem maxIdxOn_append [LE β] [DecidableLE β] [Std.IsLinearPreorder β]
    {xs ys : List α} {f : α → β} (hxs : xs ≠ []) (hys : ys ≠ []) :
    (xs ++ ys).maxIdxOn f (by simp [hxs]) =
      if f (ys.maxOn f hys) ≤ f (xs.maxOn f hxs) then
        xs.maxIdxOn f hxs
      else
        xs.length + ys.maxIdxOn f hys :=
  letI : LE β :=  (inferInstanceAs (LE β)).opposite
  minIdxOn_append hxs hys

theorem left_le_apply_maxIdxOn_append [LE β] [DecidableLE β] [Std.IsLinearPreorder β]
    {xs ys : List α} {f : α → β} (h : xs ≠ []) :
    xs.maxIdxOn f h ≤ (xs ++ ys).maxIdxOn f (by simp [h]) :=
  letI : LE β :=  (inferInstanceAs (LE β)).opposite
  left_le_apply_minIdxOn_append h

theorem apply_maxIdxOn_take_le [LE β] [DecidableLE β] [Std.IsLinearPreorder β]
    {xs : List α} {f : α → β} {i : Nat} (h : xs.take i ≠ []) :
    (xs.take i).maxIdxOn f h ≤ xs.maxIdxOn f (List.ne_nil_of_take_ne_nil h) :=
  letI : LE β :=  (inferInstanceAs (LE β)).opposite
  apply_minIdxOn_take_le h

@[simp]
theorem maxIdxOn_replicate [LE β] [DecidableLE β] [Refl (α := β) (· ≤ ·)]
    {n : Nat} {a : α} {f : α → β} (h : replicate n a ≠ []) :
    (replicate n a).maxIdxOn f h = 0 :=
  letI : LE β :=  (inferInstanceAs (LE β)).opposite
  minIdxOn_replicate h

end List
