/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.List.MinMaxOn
import Init.Data.Order.Lemmas
import Init.Data.List.Nat.TakeDrop
import Init.Data.Nat.Order
import Init.ByCases
import Init.Data.Bool
import Init.Data.Int.Lemmas
import Init.Data.Int.Order
import Init.Data.List.Sublist
import Init.Data.Nat.Lemmas
import Init.Omega

public section

open Std
open scoped OppositeOrderInstances

set_option doc.verso true
set_option linter.missingDocs true
set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace List

/--
Returns the index of an element of the non-empty list {name}`xs` that minimizes {name}`f`.
If {given}`x, y` are such that {lean}`f x = f y`, it returns the index of whichever comes first
in the list.

The correctness of this function assumes {name}`β` to be linearly pre-ordered.
-/
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

/--
Returns the index of an element of {name}`xs` that minimizes {name}`f`. If {given}`x, y`
are such that {lean}`f x = f y`, it returns the index of whichever comes first in the list.
Returns {name}`none` if the list is empty.

The correctness of this function assumes {name}`β` to be linearly pre-ordered.
-/
@[inline]
def minIdxOn? [LE β] [DecidableLE β] (f : α → β) (xs : List α) : Option Nat :=
  match xs with
  | [] => none
  | y :: ys => some ((y :: ys).minIdxOn f (nomatch ·))

/--
Returns the index of an element of the non-empty list {name}`xs` that maximizes {name}`f`.
If {given}`x, y` are such that {lean}`f x = f y`, it returns the index of whichever comes first
in the list.

The correctness of this function assumes {name}`β` to be linearly pre-ordered.
-/
@[inline]
def maxIdxOn [LE β] [DecidableLE β] (f : α → β) (xs : List α) (h : xs ≠ []) : Nat :=
  letI : LE β := LE.opposite inferInstance
  xs.minIdxOn f h

/--
Returns the index of an element of {name}`xs` that maximizes {name}`f`. If {given}`x, y`
are such that {lean}`f x = f y`, it returns the index of whichever comes first in the list.
Returns {name}`none` if the list is empty.

The correctness of this function assumes {name}`β` to be linearly pre-ordered.
-/
@[inline]
def maxIdxOn? [LE β] [DecidableLE β] (f : α → β) (xs : List α) : Option Nat :=
  letI : LE β := LE.opposite inferInstance
  xs.minIdxOn? f

protected theorem maxIdxOn_eq_minIdxOn {le : LE β} {_ : DecidableLE β} {f : α → β}
    {xs : List α} {h} :
    xs.maxIdxOn f h = (letI := le.opposite; xs.minIdxOn f h) :=
  (rfl)

private theorem minIdxOn.go_lt_length_add [LE β] [DecidableLE β] {f : α → β} {x : α}
    {i j : Nat} {xs : List α} (h : i < j) :
    List.minIdxOn.go f x i j xs < xs.length + j := by
  induction xs generalizing x i j
  · simp [go, h]
  · rename_i y ys ih
    simp only [go, length_cons, Nat.add_assoc, Nat.add_comm 1]
    split
    · exact ih (Nat.lt_succ_of_lt ‹i < j›)
    · exact ih (Nat.lt_succ_self j)

private theorem minIdxOn.go_eq_of_forall_le [LE β] [DecidableLE β] {f : α → β}
    {x : α} {i j : Nat} {xs : List α} (h : ∀ y ∈ xs, f x ≤ f y) :
    List.minIdxOn.go f x i j xs = i := by
  induction xs generalizing x i j
  · simp [go]
  · rename_i y ys ih
    simp only [go]
    split
    · apply ih
      simp_all
    · simp_all

private theorem exists_getElem_eq_of_drop_eq_cons {xs : List α} {k : Nat} {y : α} {ys : List α}
    (h : xs.drop k = y :: ys) : ∃ hlt : k < xs.length, xs[k] = y := by
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

private theorem take_succ_eq_append_of_drop_eq_cons {xs : List α} {k : Nat} {y : α}
    {ys : List α} (h : xs.drop k = y :: ys) : xs.take (k + 1) = xs.take k ++ [y] := by
  obtain ⟨hlt, rfl⟩ := exists_getElem_eq_of_drop_eq_cons h
  rw [take_succ_eq_append_getElem hlt]

private theorem minIdxOn_eq_go_drop [LE β] [DecidableLE β] [IsLinearPreorder β] {f : α → β}
    {xs : List α} (h : xs ≠ []) {k : Nat} :
    ∃ (i : Nat) (hlt : i < xs.length), i ≤ k ∧ xs[i] = (xs.take (k + 1)).minOn f (by simpa) ∧
        xs.minIdxOn f h = List.minIdxOn.go f ((xs.take (k + 1)).minOn f (by cases xs <;> simp_all)) i (k + 1) (xs.drop (k + 1)) := by
  match xs with
  | y :: ys =>
    simp only [drop_succ_cons]
    induction k
    · simp [minIdxOn]
    · rename_i k ih
      specialize ih
      obtain ⟨i, hlt, hi, ih⟩ := ih
      simp only [ih, ← drop_drop]
      simp only [length_cons] at hlt
      match h : drop k ys with
      | [] =>
        have : ys.length ≤ k := by simp_all
        simp [drop_nil, minIdxOn.go, take_of_length_le, hi, ih, hlt, this, Nat.le_succ_of_le]
      | z :: zs =>
        simp only [minIdxOn.go]
        have : take (k + 1 + 1) (y :: ys) = take (k + 1) (y :: ys) ++ [z] := by apply take_succ_eq_append_of_drop_eq_cons ‹_›
        simp only [this, List.minOn_append (xs := take (k + 1) (y :: ys)) (by simp) (cons_ne_nil _ _)]
        simp only [take_succ_cons] at this
        split
        · simp only [List.minOn_singleton, minOn_eq_left, length_cons, *]
          exact ⟨i, by omega, Nat.le_succ_of_le ‹i ≤ k›, by simp [ih], rfl⟩
        · simp only [List.minOn_singleton, not_false_eq_true, minOn_eq_right, length_cons, *]
          obtain ⟨hlt, rfl⟩ := exists_getElem_eq_of_drop_eq_cons h
          exact ⟨k + 1, by omega, Nat.le_refl _, by simp, rfl⟩

@[simp]
protected theorem minIdxOn_nil_eq_iff_true [LE β] [DecidableLE β] {f : α → β} {x : Nat}
    (h : [] ≠ []) : ([] : List α).minIdxOn f h = x ↔ True :=
  nomatch h

protected theorem minIdxOn_nil_eq_iff_false [LE β] [DecidableLE β] {f : α → β} {x : Nat}
    (h : [] ≠ []) : ([] : List α).minIdxOn f h = x ↔ False :=
  nomatch h

@[simp]
protected theorem minIdxOn_singleton [LE β] [DecidableLE β] {x : α} {f : α → β} :
    [x].minIdxOn f (of_decide_eq_false rfl) = 0 := by
  rw [minIdxOn, minIdxOn.go]

@[simp]
protected theorem minIdxOn_lt_length [LE β] [DecidableLE β] {f : α → β} {xs : List α}
    (h : xs ≠ []) : xs.minIdxOn f h < xs.length := by
  rw [minIdxOn.eq_def]
  split
  simp [minIdxOn.go_lt_length_add]

protected theorem minIdxOn_le_of_apply_getElem_le_apply_minOn [LE β] [DecidableLE β] [IsLinearPreorder β]
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
  apply List.apply_minOn_le_of_mem
  apply mem_of_mem_drop
  exact hy

protected theorem apply_minOn_lt_apply_getElem_of_lt_minIdxOn [LE β] [DecidableLE β] [LT β] [IsLinearPreorder β]
    [LawfulOrderLT β]
    {f : α → β} {xs : List α} (h : xs ≠ [])
    {k : Nat} (hk : k < xs.minIdxOn f h) :
    f (xs.minOn f h) < f (xs[k]'(by haveI := List.minIdxOn_lt_length (f := f) h; omega)) := by
  simp only [← not_le] at hk ⊢
  apply hk.imp
  apply List.minIdxOn_le_of_apply_getElem_le_apply_minOn

@[simp]
protected theorem getElem_minIdxOn [LE β] [DecidableLE β] [IsLinearPreorder β]
    {f : α → β} {xs : List α} (h : xs ≠ []) :
    xs[xs.minIdxOn f h] = xs.minOn f h := by
  obtain ⟨i, hlt, hi, heq, h'⟩ := minIdxOn_eq_go_drop (f := f) h (k := xs.length)
  simp only [drop_eq_nil_of_le (as := xs) (i := xs.length + 1) (by omega), minIdxOn.go] at h'
  simp [h', heq, take_of_length_le (l := xs) (i := xs.length + 1) (by omega)]

protected theorem le_minIdxOn_of_apply_getElem_lt_apply_getElem [LE β] [DecidableLE β] [LT β] [IsLinearPreorder β]
    [LawfulOrderLT β] {f : α → β} {xs : List α} (h : xs ≠ []) {i : Nat} (hi : i < xs.length)
    (hi' : ∀ j, (_ : j < i) → f xs[i] < f xs[j]) :
    i ≤ xs.minIdxOn f h := by
  false_or_by_contra; rename_i hgt
  simp only [not_le] at hgt
  specialize hi' _ hgt
  simp only [List.getElem_minIdxOn] at hi'
  apply (not_le.mpr hi').elim
  apply List.apply_minOn_le_of_mem
  simp

protected theorem minIdxOn_le_of_apply_getElem_le_apply_getElem [LE β] [DecidableLE β] [IsLinearPreorder β]
    {f : α → β} {xs : List α} (h : xs ≠ []) {i : Nat} (hi : i < xs.length)
    (hi' : ∀ j, (_ : j < xs.length) → f xs[i] ≤ f xs[j]) :
    xs.minIdxOn f h ≤ i := by
  apply List.minIdxOn_le_of_apply_getElem_le_apply_minOn h hi
  simp only [List.le_apply_minOn_iff, List.mem_iff_getElem]
  rintro _ ⟨j, hj, rfl⟩
  exact hi' _ hj

protected theorem minIdxOn_eq_iff [LE β] [DecidableLE β] [LT β] [IsLinearPreorder β]
    [LawfulOrderLT β]
    {f : α → β} {xs : List α} (h : xs ≠ []) {i : Nat} :
    xs.minIdxOn f h = i ↔ ∃ (h : i < xs.length),
        (∀ j, (_ : j < xs.length) → f xs[i] ≤ f xs[j]) ∧
        (∀ j, (_ : j < i) → f xs[i] < f xs[j]) := by
  apply Iff.intro
  · rintro rfl
    simp only [List.getElem_minIdxOn]
    refine ⟨List.minIdxOn_lt_length h, ?_, ?_⟩
    · simp [List.apply_minOn_le_of_mem]
    · exact fun j hj => List.apply_minOn_lt_apply_getElem_of_lt_minIdxOn h hj
  · rintro ⟨hi, h₁, h₂⟩
    apply le_antisymm
    · apply List.minIdxOn_le_of_apply_getElem_le_apply_getElem h hi h₁
    · apply List.le_minIdxOn_of_apply_getElem_lt_apply_getElem h hi h₂

protected theorem minIdxOn_eq_iff_eq_minOn [LE β] [DecidableLE β] [LT β] [IsLinearPreorder β]
    [LawfulOrderLT β] {f : α → β} {xs : List α} (h : xs ≠ []) {i : Nat} :
    xs.minIdxOn f h = i ↔ ∃ hi : i < xs.length, xs[i] = xs.minOn f h ∧
      ∀ (j : Nat) (hj : j < i), f (xs.minOn f h) < f xs[j] := by
  apply Iff.intro
  · rintro rfl
    refine ⟨List.minIdxOn_lt_length h, List.getElem_minIdxOn h, ?_⟩
    intro j hj
    exact List.apply_minOn_lt_apply_getElem_of_lt_minIdxOn h hj
  · rintro ⟨hlt, heq, h'⟩
    specialize h' (xs.minIdxOn f h)
    simp only [List.getElem_minIdxOn] at h'
    apply le_antisymm
    · apply List.minIdxOn_le_of_apply_getElem_le_apply_minOn h hlt
      simp [heq, le_refl]
    · simpa [lt_irrefl] using h'

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
    simp only [go, reduceCtorEq, ↓reduceDIte]
    split
    · rw [ih]
      split
      · simp [*]
      · simp only [List.minOn_cons, ↓reduceDIte, le_apply_minOn_iff, true_and, *]
        split
        · rfl
        · rename_i hlt
          simp only [minIdxOn]
          split
          simp only [ih, reduceCtorEq, ↓reduceDIte]
          rw [if_neg]
          · simp [minIdxOn, Nat.add_assoc, Nat.add_comm 1]
          · simp only [not_le] at hlt ⊢
            exact lt_of_lt_of_le hlt ‹_›
    · rename_i hlt
      rw [if_neg]
      · rw [minIdxOn, ih]
        split
        · simp [*, go]
        · simp only [↓reduceDIte, *]
          split
          · simp
          · simp only [Nat.add_assoc, Nat.add_comm 1]
      · simp only [not_le] at hlt ⊢
        exact lt_of_le_of_lt (List.apply_minOn_le_of_mem mem_cons_self) hlt

protected theorem minIdxOn_cons
    [LE β] [DecidableLE β] [IsLinearPreorder β] {x : α} {xs : List α} {f : α → β} :
    (x :: xs).minIdxOn f (by exact of_decide_eq_false rfl) =
      if h : xs = [] then 0
      else if f x ≤ f (xs.minOn f h) then 0
      else (xs.minIdxOn f h) + 1 := by
  simpa [List.minIdxOn] using minIdxOn.go_eq

protected theorem minIdxOn_eq_zero_iff [LE β] [DecidableLE β] [IsLinearPreorder β]
    {xs : List α} {f : α → β} (h : xs ≠ []) :
    xs.minIdxOn f h = 0 ↔ ∀ x ∈ xs, f (xs.head h) ≤ f x := by
  rw [minIdxOn.eq_def]
  split
  rename_i y ys _
  simp only [mem_cons, head_cons, forall_eq_or_imp, le_refl, true_and]
  apply Iff.intro
  · intro h
    cases ys
    · simp
    · intro a ha
      refine le_trans ?_ (List.apply_minOn_le_of_mem ha)
      simpa [minIdxOn.go_eq] using h
  · intro h
    cases ys
    · simp [minIdxOn.go]
    · simpa [minIdxOn.go_eq, List.le_apply_minOn_iff] using h

section Append

/-!
The proof of {name}`List.minOn_append` uses associativity of {name}`minOn` and applies {name}`foldl_assoc`.
The proof of {name (scope := "Init.Data.List.MinMaxIdx")}`minIdxOn_append` is analogous, but the
aggregation operation, {name (scope := "Init.Data.List.MinMaxIdx")}`combineMinIdxOn`, depends on
the length of the lists to combine. After proving associativity of the aggregation operation,
the proof closely follows the proof of {name}`foldl_assoc`.
-/

private def combineMinIdxOn [LE β] [DecidableLE β]
    (f : α → β) {xs ys : List α} (i j : Nat) (hi : i < xs.length) (hj : j < ys.length) : Nat :=
  if f xs[i] ≤ f ys[j] then
    i
  else
    xs.length + j

private theorem combineMinIdxOn_lt [LE β] [DecidableLE β]
    (f : α → β) {xs ys : List α} {i j : Nat} (hi : i < xs.length) (hj : j < ys.length) :
    combineMinIdxOn f i j hi hj < (xs ++ ys).length := by
  simp only [combineMinIdxOn]
  split <;> (simp; omega)

private theorem combineMinIdxOn_assoc [LE β] [DecidableLE β] [IsLinearPreorder β]
    {xs ys zs : List α} {i j k : Nat} {f : α → β} (hi : i < xs.length) (hj : j < ys.length)
    (hk : k < zs.length) :
    combineMinIdxOn f (combineMinIdxOn f i j _ _) k
      (combineMinIdxOn_lt f hi hj) hk = combineMinIdxOn f i (combineMinIdxOn f j k _ _) hi (combineMinIdxOn_lt f hj hk) := by
  open scoped Classical.Order in
  simp only [combineMinIdxOn]
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
      rw [not_le] at h₁ h₂
      rw [getElem_append_right (by omega)]
      simp only [Nat.add_sub_cancel_left]
      have := not_le.mpr <| lt_trans h₂ h₁
      simp [*, Nat.add_assoc]

private theorem minIdxOn_cons_aux [LE β] [DecidableLE β]
    [IsLinearPreorder β] {x : α} {xs : List α} {f : α → β} (hxs : xs ≠ []) :
    (x :: xs).minIdxOn f (by simp) =
      combineMinIdxOn f _ _
        (List.minIdxOn_lt_length (f := f) (cons_ne_nil x []))
        (List.minIdxOn_lt_length (f := f) hxs) := by
  rw [minIdxOn, combineMinIdxOn]
  simp [minIdxOn.go_eq, hxs, List.getElem_minIdxOn, Nat.add_comm 1]

private theorem minIdxOn_append_aux [LE β] [DecidableLE β]
    [IsLinearPreorder β] {xs ys : List α} {f : α → β} (hxs : xs ≠ []) (hys : ys ≠ []) :
    (xs ++ ys).minIdxOn f (by simp [hxs]) =
      combineMinIdxOn f _ _
        (List.minIdxOn_lt_length (f := f) hxs)
        (List.minIdxOn_lt_length (f := f) hys) := by
  induction xs
  · contradiction
  · rename_i x xs ih
    match xs with
    | [] => simp [minIdxOn_cons_aux (xs := ys) ‹_›]
    | z :: zs =>
      simp +singlePass only [cons_append]
      simp only [minIdxOn_cons_aux (xs := z :: zs ++ ys) (by simp), ih (by simp),
        minIdxOn_cons_aux (xs := z :: zs) (by simp), combineMinIdxOn_assoc]

protected theorem minIdxOn_append [LE β] [DecidableLE β] [IsLinearPreorder β]
    {xs ys : List α} {f : α → β} (hxs : xs ≠ []) (hys : ys ≠ []) :
    (xs ++ ys).minIdxOn f (by simp [hxs]) =
      if f (xs.minOn f hxs) ≤ f (ys.minOn f hys) then
        xs.minIdxOn f hxs
      else
        xs.length + ys.minIdxOn f hys := by
  simp [minIdxOn_append_aux hxs hys, combineMinIdxOn, List.getElem_minIdxOn]

end Append

protected theorem left_le_minIdxOn_append [LE β] [DecidableLE β] [IsLinearPreorder β]
    {xs ys : List α} {f : α → β} (h : xs ≠ []) :
    xs.minIdxOn f h ≤ (xs ++ ys).minIdxOn f (by simp [h]) := by
  by_cases hys : ys = []
  · simp [hys]
  · rw [List.minIdxOn_append h hys]
    split
    · apply Nat.le_refl
    · have := List.minIdxOn_lt_length (f := f) h
      omega

protected theorem minIdxOn_take_le [LE β] [DecidableLE β] [IsLinearPreorder β]
    {xs : List α} {f : α → β} {i : Nat} (h : xs.take i ≠ []) :
    (xs.take i).minIdxOn f h ≤ xs.minIdxOn f (List.ne_nil_of_take_ne_nil h) := by
  have := take_append_drop i xs
  conv => rhs; simp +singlePass only [← this]
  apply List.left_le_minIdxOn_append

@[simp]
protected theorem minIdxOn_replicate [LE β] [DecidableLE β] [Refl (α := β) (· ≤ ·)]
    {n : Nat} {a : α} {f : α → β} (h : replicate n a ≠ []) :
    (replicate n a).minIdxOn f h = 0 := by
  match n with
  | 0 => simp at h
  | n + 1 =>
    simp only [minIdxOn, replicate_succ]
    generalize 1 = j
    induction n generalizing j
    · simp [minIdxOn.go]
    · simp only [replicate_succ, minIdxOn.go] at *
      split
      · simp [*]
      · have := le_refl (f a)
        contradiction

@[simp]
protected theorem maxIdxOn_nil_eq_iff_true [LE β] [DecidableLE β] {f : α → β} {x : Nat}
    (h : [] ≠ []) : ([] : List α).maxIdxOn f h = x ↔ True :=
  nomatch h

protected theorem maxIdxOn_nil_eq_iff_false [LE β] [DecidableLE β] {f : α → β} {x : Nat}
    (h : [] ≠ []) : ([] : List α).maxIdxOn f h = x ↔ False :=
  nomatch h

@[simp]
protected theorem maxIdxOn_singleton [LE β] [DecidableLE β] {x : α} {f : α → β} :
    [x].maxIdxOn f (of_decide_eq_false rfl) = 0 :=
  letI : LE β := (inferInstanceAs (LE β)).opposite
  List.minIdxOn_singleton

@[simp]
protected theorem maxIdxOn_lt_length [LE β] [DecidableLE β] {f : α → β} {xs : List α}
    (h : xs ≠ []) : xs.maxIdxOn f h < xs.length :=
  letI : LE β := (inferInstanceAs (LE β)).opposite
  List.minIdxOn_lt_length h

protected theorem maxIdxOn_le_of_apply_getElem_le_apply_maxOn [LE β] [DecidableLE β] [IsLinearPreorder β]
    {f : α → β} {xs : List α} (h : xs ≠ [])
    {k : Nat} (hi : k < xs.length) (hle : f (xs.maxOn f h) ≤ f xs[k]) :
    xs.maxIdxOn f h ≤ k := by
  simp only [List.maxIdxOn_eq_minIdxOn, List.maxOn_eq_minOn] at hle ⊢
  letI : LE β := (inferInstanceAs (LE β)).opposite
  exact List.minIdxOn_le_of_apply_getElem_le_apply_minOn h hi (by simpa [LE.le_opposite_iff] using hle)

protected theorem apply_maxOn_lt_apply_getElem_of_lt_maxIdxOn [LE β] [DecidableLE β] [LT β] [IsLinearPreorder β]
    [LawfulOrderLT β]
    {f : α → β} {xs : List α} (h : xs ≠ [])
    {k : Nat} (hk : k < xs.maxIdxOn f h) :
    f (xs[k]'(by haveI := List.maxIdxOn_lt_length (f := f) h; omega)) < f (xs.maxOn f h) := by
  simp only [List.maxIdxOn_eq_minIdxOn, List.maxOn_eq_minOn] at hk ⊢
  letI : LE β := LE.opposite inferInstance
  letI : LT β := LT.opposite inferInstance
  simpa [LT.lt_opposite_iff] using List.apply_minOn_lt_apply_getElem_of_lt_minIdxOn (f := f) h hk

@[simp]
protected theorem getElem_maxIdxOn [LE β] [DecidableLE β] [IsLinearPreorder β]
    {f : α → β} {xs : List α} (h : xs ≠ []) :
    xs[xs.maxIdxOn f h] = xs.maxOn f h := by
  simp only [List.maxIdxOn_eq_minIdxOn, List.maxOn_eq_minOn]
  letI : LE β := (inferInstanceAs (LE β)).opposite
  exact List.getElem_minIdxOn h

protected theorem le_maxIdxOn_of_apply_getElem_lt_apply_getElem [LE β] [DecidableLE β] [LT β]
    [IsLinearPreorder β] [LawfulOrderLT β] {f : α → β} {xs : List α} (h : xs ≠ []) {i : Nat}
    (hi : i < xs.length) (hi' : ∀ j, (_ : j < i) → f xs[j] < f xs[i]) :
    i ≤ xs.maxIdxOn f h := by
  simp only [List.maxIdxOn_eq_minIdxOn]
  letI : LE β := LE.opposite inferInstance
  letI : LT β := LT.opposite inferInstance
  simpa [LE.le_opposite_iff] using List.le_minIdxOn_of_apply_getElem_lt_apply_getElem h hi
      (by simpa [LT.lt_opposite_iff] using hi')

protected theorem maxIdxOn_le_of_apply_getElem_le_apply_getElem [LE β] [DecidableLE β] [IsLinearPreorder β]
    {f : α → β} {xs : List α} (h : xs ≠ []) {i : Nat} (hi : i < xs.length)
    (hi' : ∀ j, (_ : j < xs.length) → f xs[j] ≤ f xs[i]) :
    xs.maxIdxOn f h ≤ i := by
  simp only [List.maxIdxOn_eq_minIdxOn]
  letI : LE β := LE.opposite inferInstance
  simpa [LE.le_opposite_iff] using List.minIdxOn_le_of_apply_getElem_le_apply_getElem (f := f) h hi
      (by simpa [LE.le_opposite_iff] using hi')

protected theorem maxIdxOn_eq_iff [LE β] [DecidableLE β] [LT β] [IsLinearPreorder β]
    [LawfulOrderLT β]
    {f : α → β} {xs : List α} (h : xs ≠ []) {i : Nat} :
    xs.maxIdxOn f h = i ↔ ∃ (h : i < xs.length),
        (∀ j, (_ : j < xs.length) → f xs[j] ≤ f xs[i]) ∧
        (∀ j, (_ : j < i) → f xs[j] < f xs[i]) := by
  simp only [List.maxIdxOn_eq_minIdxOn]
  letI : LE β := LE.opposite inferInstance
  letI : LT β := LT.opposite inferInstance
  simpa [LE.le_opposite_iff, LT.lt_opposite_iff] using List.minIdxOn_eq_iff (f := f) h

protected theorem maxIdxOn_eq_iff_eq_maxOn [LE β] [DecidableLE β] [LT β] [IsLinearPreorder β]
    [LawfulOrderLT β] {f : α → β} {xs : List α} (h : xs ≠ []) {i : Nat} :
    xs.maxIdxOn f h = i ↔ ∃ hi : i < xs.length, xs[i] = xs.maxOn f h ∧
      ∀ (j : Nat) (hj : j < i), f xs[j] < f (xs.maxOn f h) := by
  simp only [List.maxIdxOn_eq_minIdxOn, List.maxOn_eq_minOn]
  letI : LE β := LE.opposite inferInstance
  letI : LT β := LT.opposite inferInstance
  simpa [LT.lt_opposite_iff] using List.minIdxOn_eq_iff_eq_minOn (f := f) h

protected theorem maxIdxOn_cons
    [LE β] [DecidableLE β] [IsLinearPreorder β] {x : α} {xs : List α} {f : α → β} :
    (x :: xs).maxIdxOn f (by exact of_decide_eq_false rfl) =
      if h : xs = [] then 0
      else if f (xs.maxOn f h) ≤ f x then 0
      else (xs.maxIdxOn f h) + 1 := by
  simp only [List.maxIdxOn_eq_minIdxOn, List.maxOn_eq_minOn]
  letI : LE β := (inferInstanceAs (LE β)).opposite
  simpa [LE.le_opposite_iff] using List.minIdxOn_cons (f := f)

protected theorem maxIdxOn_eq_zero_iff [LE β] [DecidableLE β] [IsLinearPreorder β]
    {xs : List α} {f : α → β} (h : xs ≠ []) :
    xs.maxIdxOn f h = 0 ↔ ∀ x ∈ xs, f x ≤ f (xs.head h) := by
  simp only [List.maxIdxOn_eq_minIdxOn]
  letI : LE β := (inferInstanceAs (LE β)).opposite
  simpa [LE.le_opposite_iff] using List.minIdxOn_eq_zero_iff h (f := f)

protected theorem maxIdxOn_append [LE β] [DecidableLE β] [IsLinearPreorder β]
    {xs ys : List α} {f : α → β} (hxs : xs ≠ []) (hys : ys ≠ []) :
    (xs ++ ys).maxIdxOn f (by simp [hxs]) =
      if f (ys.maxOn f hys) ≤ f (xs.maxOn f hxs) then
        xs.maxIdxOn f hxs
      else
        xs.length + ys.maxIdxOn f hys := by
  simp only [List.maxIdxOn_eq_minIdxOn, List.maxOn_eq_minOn]
  letI : LE β := (inferInstanceAs (LE β)).opposite
  simpa [LE.le_opposite_iff] using List.minIdxOn_append hxs hys (f := f)

protected theorem left_le_maxIdxOn_append [LE β] [DecidableLE β] [IsLinearPreorder β]
    {xs ys : List α} {f : α → β} (h : xs ≠ []) :
    xs.maxIdxOn f h ≤ (xs ++ ys).maxIdxOn f (by simp [h]) :=
  letI : LE β := (inferInstanceAs (LE β)).opposite
  List.left_le_minIdxOn_append h

protected theorem maxIdxOn_take_le [LE β] [DecidableLE β] [IsLinearPreorder β]
    {xs : List α} {f : α → β} {i : Nat} (h : xs.take i ≠ []) :
    (xs.take i).maxIdxOn f h ≤ xs.maxIdxOn f (List.ne_nil_of_take_ne_nil h) :=
  letI : LE β := (inferInstanceAs (LE β)).opposite
  List.minIdxOn_take_le h

@[simp]
protected theorem maxIdxOn_replicate [LE β] [DecidableLE β] [Refl (α := β) (· ≤ ·)]
    {n : Nat} {a : α} {f : α → β} (h : replicate n a ≠ []) :
    (replicate n a).maxIdxOn f h = 0 :=
  letI : LE β := (inferInstanceAs (LE β)).opposite
  List.minIdxOn_replicate h

@[simp]
protected theorem minIdxOn?_nil [LE β] [DecidableLE β] {f : α → β} :
    ([] : List α).minIdxOn? f = none :=
  (rfl)

@[simp]
protected theorem minIdxOn?_singleton [LE β] [DecidableLE β] {x : α} {f : α → β} :
    [x].minIdxOn? f = some 0 :=
  (rfl)

@[simp]
protected theorem isSome_minIdxOn?_iff [LE β] [DecidableLE β] {f : α → β} {xs : List α} :
    (xs.minIdxOn? f).isSome ↔ xs ≠ [] := by
  cases xs <;> simp [minIdxOn?]

protected theorem minIdxOn_eq_get_minIdxOn? [LE β] [DecidableLE β] {f : α → β} {xs : List α}
    (h : xs ≠ []) : xs.minIdxOn f h = (xs.minIdxOn? f).get (List.isSome_minIdxOn?_iff.mpr h) := by
  match xs with
  | [] => contradiction
  | _ :: _ => simp [minIdxOn?]

@[simp]
protected theorem get_minIdxOn?_eq_minIdxOn [LE β] [DecidableLE β] {f : α → β} {xs : List α}
    (h : (xs.minIdxOn? f).isSome) :
    (xs.minIdxOn? f).get h = xs.minIdxOn f (List.isSome_minIdxOn?_iff.mp h) := by
  rw [List.minIdxOn_eq_get_minIdxOn?]

protected theorem minIdxOn?_eq_some_minIdxOn [LE β] [DecidableLE β] {f : α → β} {xs : List α}
    (h : xs ≠ []) : xs.minIdxOn? f = some (xs.minIdxOn f h) := by
  match xs with
  | [] => contradiction
  | _ :: _ => simp [minIdxOn?]

protected theorem minIdxOn_eq_of_minIdxOn?_eq_some
    [LE β] [DecidableLE β] {f : α → β} {xs : List α} {i : Nat} (h : xs.minIdxOn? f = some i) :
    xs.minIdxOn f (List.isSome_minIdxOn?_iff.mp (Option.isSome_of_eq_some h)) = i := by
  have h' := List.isSome_minIdxOn?_iff.mp (Option.isSome_of_eq_some h)
  rwa [List.minIdxOn?_eq_some_minIdxOn h', Option.some.injEq] at h

protected theorem isSome_minIdxOn?_of_mem
    [LE β] [DecidableLE β] {f : α → β} {xs : List α} {x : α} (h : x ∈ xs) :
    (xs.minIdxOn? f).isSome := by
  apply List.isSome_minIdxOn?_iff.mpr
  exact ne_nil_of_mem h

protected theorem minIdxOn?_cons_eq_some_minIdxOn
    [LE β] [DecidableLE β] {f : α → β} {x : α} {xs : List α} :
    (x :: xs).minIdxOn? f = some ((x :: xs).minIdxOn f (nomatch ·)) := by
  simp [List.minIdxOn?_eq_some_minIdxOn]

protected theorem minIdxOn?_eq_if
    [LE β] [DecidableLE β] {f : α → β} {xs : List α} :
    xs.minIdxOn? f =
      if h : xs ≠ [] then
        some (xs.minIdxOn f h)
      else
        none := by
  cases xs <;> simp [List.minIdxOn?_cons_eq_some_minIdxOn]

protected theorem minIdxOn?_cons
    [LE β] [DecidableLE β] [IsLinearPreorder β] {f : α → β} {x : α} {xs : List α} :
    (x :: xs).minIdxOn? f = some
      (if h : xs = [] then 0
        else if f x ≤ f (xs.minOn f h) then 0
        else (xs.minIdxOn f h) + 1) := by
  simp [List.minIdxOn?_eq_some_minIdxOn, List.minIdxOn_cons]

protected theorem ne_nil_of_minIdxOn?_eq_some
    [LE β] [DecidableLE β] {f : α → β} {k : Nat} {xs : List α} (h : xs.minIdxOn? f = some k) :
    xs ≠ [] := by
  rintro rfl
  simp at h

protected theorem lt_length_of_minIdxOn?_eq_some [LE β] [DecidableLE β] {f : α → β}
    {xs : List α} (h : xs.minIdxOn? f = some i) : i < xs.length := by
  have hne : xs ≠ [] := List.ne_nil_of_minIdxOn?_eq_some h
  rw [List.minIdxOn?_eq_some_minIdxOn hne] at h
  have := List.minIdxOn_lt_length (f := f) hne
  simp_all

@[simp]
protected theorem get_minIdxOn?_lt_length [LE β] [DecidableLE β] {f : α → β} {xs : List α}
    (h : (xs.minIdxOn? f).isSome) : (xs.minIdxOn? f).get h < xs.length := by
  rw [List.get_minIdxOn?_eq_minIdxOn]
  apply List.minIdxOn_lt_length

@[simp]
protected theorem getElem_get_minIdxOn? [LE β] [DecidableLE β] [IsLinearPreorder β]
    {f : α → β} {xs : List α} (h : (xs.minIdxOn? f).isSome) :
    xs[(xs.minIdxOn? f).get h] = xs.minOn f (List.isSome_minIdxOn?_iff.mp h) := by
  rw [getElem_congr rfl (List.get_minIdxOn?_eq_minIdxOn _), List.getElem_minIdxOn]

protected theorem minIdxOn?_eq_some_zero_iff [LE β] [DecidableLE β] [IsLinearPreorder β]
    {xs : List α} {f : α → β} :
    xs.minIdxOn? f = some 0 ↔ ∃ h : xs ≠ [], ∀ x ∈ xs, f (xs.head h) ≤ f x := by
  simp [Option.eq_some_iff_get_eq, List.minIdxOn_eq_zero_iff]

protected theorem minIdxOn?_replicate [LE β] [DecidableLE β] [Refl (α := β) (· ≤ ·)]
    {n : Nat} {a : α} {f : α → β} :
    (replicate n a).minIdxOn? f = if n = 0 then none else some 0 := by
  simp [List.minIdxOn?_eq_if]

@[simp]
protected theorem minIdxOn?_replicate_of_pos [LE β] [DecidableLE β] [Refl (α := β) (· ≤ ·)]
    {n : Nat} {a : α} {f : α → β} (h : 0 < n) :
    (replicate n a).minIdxOn? f = some 0 := by
  simp [List.minIdxOn?_replicate, Nat.ne_zero_of_lt h]

/-! ### maxIdxOn? -/

protected theorem maxIdxOn?_eq_minIdxOn? {le : LE β} {_ : DecidableLE β} {f : α → β}
    {xs : List α} :
    xs.maxIdxOn? f = (letI := le.opposite; xs.minIdxOn? f) :=
  (rfl)

@[simp]
protected theorem maxIdxOn?_nil [LE β] [DecidableLE β] {f : α → β} :
    ([] : List α).maxIdxOn? f = none :=
  letI : LE β := LE.opposite inferInstance
  List.minIdxOn?_nil

@[simp]
protected theorem maxIdxOn?_singleton [LE β] [DecidableLE β] {x : α} {f : α → β} :
    [x].maxIdxOn? f = some 0 :=
  letI : LE β := LE.opposite inferInstance
  List.minIdxOn?_singleton

@[simp]
protected theorem isSome_maxIdxOn?_iff [LE β] [DecidableLE β] {f : α → β} {xs : List α} :
    (xs.maxIdxOn? f).isSome ↔ xs ≠ [] := by
  letI : LE β := LE.opposite inferInstance
  exact List.isSome_minIdxOn?_iff

protected theorem maxIdxOn_eq_get_maxIdxOn? [LE β] [DecidableLE β] {f : α → β} {xs : List α}
    (h : xs ≠ []) : xs.maxIdxOn f h = (xs.maxIdxOn? f).get (List.isSome_maxIdxOn?_iff.mpr h) := by
  letI : LE β := LE.opposite inferInstance
  exact List.minIdxOn_eq_get_minIdxOn? h

@[simp]
protected theorem get_maxIdxOn?_eq_maxIdxOn [LE β] [DecidableLE β] {f : α → β} {xs : List α}
    (h : (xs.maxIdxOn? f).isSome) :
    (xs.maxIdxOn? f).get h = xs.maxIdxOn f (List.isSome_maxIdxOn?_iff.mp h) := by
  letI : LE β := LE.opposite inferInstance
  exact List.get_minIdxOn?_eq_minIdxOn h

protected theorem maxIdxOn?_eq_some_maxIdxOn [LE β] [DecidableLE β] {f : α → β} {xs : List α}
    (h : xs ≠ []) : xs.maxIdxOn? f = some (xs.maxIdxOn f h) := by
  letI : LE β := LE.opposite inferInstance
  exact List.minIdxOn?_eq_some_minIdxOn h

protected theorem maxIdxOn_eq_of_maxIdxOn?_eq_some
    [LE β] [DecidableLE β] {f : α → β} {xs : List α} {i : Nat} (h : xs.maxIdxOn? f = some i) :
    xs.maxIdxOn f (List.isSome_maxIdxOn?_iff.mp (Option.isSome_of_eq_some h)) = i := by
  letI : LE β := LE.opposite inferInstance
  exact List.minIdxOn_eq_of_minIdxOn?_eq_some h

protected theorem isSome_maxIdxOn?_of_mem
    [LE β] [DecidableLE β] {f : α → β} {xs : List α} {x : α} (h : x ∈ xs) :
    (xs.maxIdxOn? f).isSome := by
  letI : LE β := LE.opposite inferInstance
  exact List.isSome_minIdxOn?_of_mem h

protected theorem maxIdxOn?_cons_eq_some_maxIdxOn
    [LE β] [DecidableLE β] {f : α → β} {x : α} {xs : List α} :
    (x :: xs).maxIdxOn? f = some ((x :: xs).maxIdxOn f (nomatch ·)) := by
  letI : LE β := LE.opposite inferInstance
  exact List.minIdxOn?_cons_eq_some_minIdxOn

protected theorem maxIdxOn?_eq_if
    [LE β] [DecidableLE β] {f : α → β} {xs : List α} :
    xs.maxIdxOn? f =
      if h : xs ≠ [] then
        some (xs.maxIdxOn f h)
      else
        none := by
  letI : LE β := LE.opposite inferInstance
  exact List.minIdxOn?_eq_if

protected theorem maxIdxOn?_cons
    [LE β] [DecidableLE β] [IsLinearPreorder β] {f : α → β} {x : α} {xs : List α} :
    (x :: xs).maxIdxOn? f = some
      (if h : xs = [] then 0
        else if f (xs.maxOn f h) ≤ f x then 0
        else (xs.maxIdxOn f h) + 1) := by
  simp only [List.maxIdxOn_eq_minIdxOn, List.maxOn_eq_minOn]
  letI : LE β := LE.opposite inferInstance
  simpa [LE.le_opposite_iff] using List.minIdxOn?_cons (f := f)

protected theorem ne_nil_of_maxIdxOn?_eq_some
    [LE β] [DecidableLE β] {f : α → β} {k : Nat} {xs : List α} (h : xs.maxIdxOn? f = some k) :
    xs ≠ [] := by
  letI : LE β := LE.opposite inferInstance
  exact List.ne_nil_of_minIdxOn?_eq_some (by simpa only [List.maxIdxOn?_eq_minIdxOn?] using h)

protected theorem lt_length_of_maxIdxOn?_eq_some [LE β] [DecidableLE β] {f : α → β}
    {xs : List α} (h : xs.maxIdxOn? f = some i) : i < xs.length := by
  letI : LE β := LE.opposite inferInstance
  exact List.lt_length_of_minIdxOn?_eq_some h

@[simp]
protected theorem get_maxIdxOn?_lt_length [LE β] [DecidableLE β] {f : α → β} {xs : List α}
    (h : (xs.maxIdxOn? f).isSome) : (xs.maxIdxOn? f).get h < xs.length := by
  letI : LE β := LE.opposite inferInstance
  exact List.get_minIdxOn?_lt_length h

@[simp]
protected theorem getElem_get_maxIdxOn? [LE β] [DecidableLE β] [IsLinearPreorder β]
    {f : α → β} {xs : List α} (h : (xs.maxIdxOn? f).isSome) :
    xs[(xs.maxIdxOn? f).get h] = xs.maxOn f (List.isSome_maxIdxOn?_iff.mp h) := by
  simp only [List.maxIdxOn?_eq_minIdxOn?, List.maxOn_eq_minOn]
  letI : LE β := LE.opposite inferInstance
  exact List.getElem_get_minIdxOn? h

protected theorem maxIdxOn?_eq_some_zero_iff [LE β] [DecidableLE β] [IsLinearPreorder β]
    {xs : List α} {f : α → β} :
    xs.maxIdxOn? f = some 0 ↔ ∃ h : xs ≠ [], ∀ x ∈ xs, f x ≤ f (xs.head h) := by
  simp only [List.maxIdxOn?_eq_minIdxOn?]
  letI : LE β := LE.opposite inferInstance
  simpa [LE.le_opposite_iff] using List.minIdxOn?_eq_some_zero_iff (f := f)

protected theorem maxIdxOn?_replicate [LE β] [DecidableLE β] [Refl (α := β) (· ≤ ·)]
    {n : Nat} {a : α} {f : α → β} :
    (replicate n a).maxIdxOn? f = if n = 0 then none else some 0 := by
  letI : LE β := LE.opposite inferInstance
  exact List.minIdxOn?_replicate

@[simp]
protected theorem maxIdxOn?_replicate_of_pos [LE β] [DecidableLE β] [Refl (α := β) (· ≤ ·)]
    {n : Nat} {a : α} {f : α → β} (h : 0 < n) :
    (replicate n a).maxIdxOn? f = some 0 := by
  letI : LE β := LE.opposite inferInstance
  exact List.minIdxOn?_replicate_of_pos h

end List
