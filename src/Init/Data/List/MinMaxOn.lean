/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Order.MinMaxOn
public import Init.Data.Int.OfNat
public import Init.Data.List.Lemmas
public import Init.Data.List.TakeDrop
import Init.Data.Order.Lemmas
import Init.Data.List.Sublist
import Init.Data.List.MinMax
import Init.Data.Order.Opposite

set_option doc.verso true
set_option linter.missingDocs true
set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

public section

open Std
open scoped OppositeOrderInstances

namespace List

/--
Returns an element of the non-empty list {name}`l` that minimizes {name}`f`. If {given}`x, y` are
such that {lean}`f x = f y`, it returns whichever comes first in the list.

The correctness of this function assumes {name}`β` to be linearly pre-ordered.
The property that {name}`List.minOn` is the first minimizer in the list is guaranteed by the lemma
{name (scope := "Init.Data.List.MinMaxIdx")}`List.getElem_minIdxOn`.
-/
@[inline, suggest_for List.argmin]
protected def minOn [LE β] [DecidableLE β] (f : α → β) (l : List α) (h : l ≠ []) : α :=
  match l with
  | x :: xs => xs.foldl (init := x) (minOn f)

/--
Returns an element of the non-empty list {name}`l` that maximizes {name}`f`. If {given}`x, y` are
such that {lean}`f x = f y`, it returns whichever comes first in the list.

The correctness of this function assumes {name}`β` to be linearly pre-ordered.
The property that {name}`List.maxOn` is the first maximizer in the list is guaranteed by the lemma
{name (scope := "Init.Data.List.MinMaxIdx")}`List.getElem_maxIdxOn`.
-/
@[inline, suggest_for List.argmax]
protected def maxOn [i : LE β] [DecidableLE β] (f : α → β) (l : List α) (h : l ≠ []) : α :=
  letI : LE β := i.opposite
  l.minOn f h

/--
Returns an element of {name}`l` that minimizes {name}`f`. If {given}`x, y` are such that
{lean}`f x = f y`, it returns whichever comes first in the list. Returns {name}`none` if the list is
empty.

The correctness of this function assumes {name}`β` to be linearly pre-ordered.
The property that {name}`List.minOn?` is the first minimizer in the list is guaranteed by the lemma
{name (scope := "Init.Data.List.MinMaxIdx")}`List.getElem_get_minIdxOn?`
-/
@[inline, suggest_for List.argmin? List.argmin] -- Mathlib's `List.argmin` returns an `Option α`
protected def minOn? [LE β] [DecidableLE β] (f : α → β) (l : List α) : Option α :=
  match l with
  | [] => none
  | x :: xs => some (xs.foldl (init := x) (minOn f))

/--
Returns an element of {name}`l` that maximizes {name}`f`. If {given}`x, y` are such that
{lean}`f x = f y`, it returns whichever comes first in the list. Returns {name}`none` if the list is
empty.

The correctness of this function assumes {name}`β` to be linearly pre-ordered.
The property that {name}`List.maxOn?` is the first minimizer in the list is guaranteed by the lemma
{name (scope := "Init.Data.List.MinMaxIdx")}`List.getElem_get_maxIdxOn?`.
-/
@[inline, suggest_for List.argmax? List.argmax] -- Mathlib's `List.argmax` returns an `Option α`
protected def maxOn? [i : LE β] [DecidableLE β] (f : α → β) (l : List α) : Option α :=
  letI : LE β := i.opposite
  l.minOn? f

/-! ### minOn -/

@[simp]
protected theorem minOn_singleton [LE β] [DecidableLE β] {x : α} {f : α → β} :
    [x].minOn f (of_decide_eq_false rfl) = x := by
  simp [List.minOn]

protected theorem minOn_cons
    [LE β] [DecidableLE β] [IsLinearPreorder β] {x : α} {xs : List α} {f : α → β} :
    (x :: xs).minOn f (by exact of_decide_eq_false rfl) =
      if h : xs = [] then x else minOn f x (xs.minOn f h) := by
  simp only [List.minOn]
  match xs with
  | [] => simp
  | y :: xs => simp [foldl_assoc]

@[simp]
protected theorem minOn_id [Min α] [LE α] [DecidableLE α] [LawfulOrderLeftLeaningMin α]
    {xs : List α} (h : xs ≠ []) :
    xs.minOn id h = xs.min h := by
  have : minOn (α := α) id = min := by ext; apply minOn_id
  simp only [List.minOn, List.min, this]
  match xs with
  | _ :: _ => simp

@[simp]
protected theorem minOn_mem [LE β] [DecidableLE β] {xs : List α}
    {f : α → β} {h : xs ≠ []} : xs.minOn f h ∈ xs := by
  simp only [List.minOn]
  match xs with
  | x :: xs =>
    fun_induction xs.foldl (init := x) (_root_.minOn f)
    · simp
    · rename_i x y _ ih
      simp only [ne_eq, reduceCtorEq, not_false_eq_true, mem_cons, forall_const, foldl_cons] at ih ⊢
      cases ih <;> rename_i heq
      · cases minOn_eq_or (f := f) (x := x) (y := y) <;> simp_all
      · simp [*]

protected theorem apply_minOn_le_of_mem [LE β] [DecidableLE β] [IsLinearPreorder β]
    {xs : List α} {f : α → β} {y : α} (hx : y ∈ xs) :
    f (xs.minOn f (List.ne_nil_of_mem hx)) ≤ f y := by
  have h : xs ≠ [] := List.ne_nil_of_mem hx
  simp only [List.minOn]
  match xs with
  | x :: xs =>
    fun_induction xs.foldl (init := x) (_root_.minOn f) generalizing y
    · simp only [mem_cons] at hx
      simp_all
    · rename_i x y _ ih
      simp at ih ⊢
      rcases mem_cons.mp hx with rfl | hx
      · exact le_trans ih.1 apply_minOn_le_left
      · rcases mem_cons.mp hx with rfl | hx
        · exact le_trans ih.1 apply_minOn_le_right
        · apply ih.2
          assumption

protected theorem le_apply_minOn_iff [LE β] [DecidableLE β] [IsLinearPreorder β]
    {xs : List α} {f : α → β} (h : xs ≠ []) {b : β} :
    b ≤ f (xs.minOn f h) ↔ ∀ x ∈ xs, b ≤ f x := by
  match xs with
  | x :: xs =>
    rw [List.minOn]
    induction xs generalizing x
    · simp
    · rw [foldl_cons, foldl_assoc, le_apply_minOn_iff]
      simp_all

protected theorem apply_minOn_le_iff [LE β] [DecidableLE β] [IsLinearPreorder β]
    {xs : List α} {f : α → β} (h : xs ≠ []) {b : β} :
    f (xs.minOn f h) ≤ b ↔ ∃ x ∈ xs, f x ≤ b := by
  apply Iff.intro
  · intro h
    match xs with
    | x :: xs =>
      rw [List.minOn] at h
      induction xs generalizing x
      · simpa using h
      · rename_i y ys ih _
        rw [foldl_cons] at h
        specialize ih (minOn f x y) (by simp) h
        obtain ⟨z, hm, hle⟩ := ih
        rcases mem_cons.mp hm with rfl | hm
        · cases minOn_eq_or (f := f) (x := x) (y := y)
          · exact ⟨x, by simp_all⟩
          · exact ⟨y, by simp_all⟩
        · exact ⟨z, by simp_all⟩
  · rintro ⟨x, hm, hx⟩
    exact le_trans (List.apply_minOn_le_of_mem hm) hx

protected theorem lt_apply_minOn_iff
     [LE β] [DecidableLE β] [LT β] [IsLinearPreorder β] [LawfulOrderLT β]
    {xs : List α} {f : α → β} (h : xs ≠ []) {b : β} :
    b < f (xs.minOn f h) ↔ ∀ x ∈ xs, b < f x := by
  simpa [not_le] using not_congr <| xs.apply_minOn_le_iff (f := f) h (b := b)

protected theorem apply_minOn_lt_iff
     [LE β] [DecidableLE β] [LT β] [IsLinearPreorder β] [LawfulOrderLT β]
    {xs : List α} {f : α → β} (h : xs ≠ []) {b : β} :
    f (xs.minOn f h) < b ↔ ∃ x ∈ xs, f x < b := by
  simpa [not_le] using not_congr <| xs.le_apply_minOn_iff (f := f) h (b := b)

protected theorem apply_minOn_le_apply_minOn_of_subset [LE β] [DecidableLE β]
    [IsLinearPreorder β] {xs ys : List α} {f : α → β} (hxs : ys ⊆ xs) (hys : ys ≠ []) :
    haveI : xs ≠ [] := by intro h; rw [h] at hxs; simp_all [subset_nil]
    f (xs.minOn f this) ≤ f (ys.minOn f hys) := by
  rw [List.le_apply_minOn_iff]
  intro x hx
  exact List.apply_minOn_le_of_mem (hxs hx)

protected theorem le_apply_minOn_take [LE β] [DecidableLE β] [IsLinearPreorder β]
    {xs : List α} {f : α → β} {i : Nat} (h : xs.take i ≠ []) :
    f (xs.minOn f (List.ne_nil_of_take_ne_nil h)) ≤ f ((xs.take i).minOn f h) := by
  apply List.apply_minOn_le_apply_minOn_of_subset
  apply take_subset

protected theorem apply_minOn_append_le_left [LE β] [DecidableLE β] [IsLinearPreorder β]
    {xs ys : List α} {f : α → β} (h : xs ≠ []) :
    f ((xs ++ ys).minOn f (append_ne_nil_of_left_ne_nil h ys)) ≤
      f (xs.minOn f h) := by
  apply List.apply_minOn_le_apply_minOn_of_subset
  apply subset_append_left

protected theorem apply_minOn_append_le_right [LE β] [DecidableLE β] [IsLinearPreorder β]
    {xs ys : List α} {f : α → β} (h : ys ≠ []) :
    f ((xs ++ ys).minOn f (append_ne_nil_of_right_ne_nil xs h)) ≤
      f (ys.minOn f h) := by
  apply List.apply_minOn_le_apply_minOn_of_subset
  apply subset_append_right

@[simp]
protected theorem minOn_append [LE β] [DecidableLE β] [IsLinearPreorder β] {xs ys : List α}
    {f : α → β} (hxs : xs ≠ []) (hys : ys ≠ []) :
    (xs ++ ys).minOn f (by simp [hxs]) = minOn f (xs.minOn f hxs) (ys.minOn f hys) := by
  match xs, ys with
  | x :: xs, y :: ys => simp [List.minOn, foldl_assoc]

protected theorem minOn_eq_head [LE β] [DecidableLE β] [IsLinearPreorder β]
    {xs : List α} {f : α → β} (h : xs ≠ []) (h' : ∀ x ∈ xs, f (xs.head h) ≤ f x) :
    xs.minOn f h = xs.head h := by
  match xs with
  | x :: xs =>
    simp only [List.minOn]
    induction xs
    · simp
    · simp only [foldl_cons, head_cons]
      rw [minOn_eq_left] <;> simp_all

protected theorem min_map
    [LE β] [DecidableLE β] [Min β] [IsLinearPreorder β] [LawfulOrderLeftLeaningMin β] {xs : List α}
    {f : α → β} (h : xs ≠ []) :
    (xs.map f).min (by simpa) = f (xs.minOn f h) := by
  match xs with
  | x :: xs =>
    simp only [List.minOn, map_cons, List.min, foldl_map]
    rw [foldl_hom]
    simp [min_apply]

@[simp]
protected theorem minOn_replicate [LE β] [DecidableLE β] [IsLinearPreorder β]
    {n : Nat} {a : α} {f : α → β} (h : replicate n a ≠ []) :
    (replicate n a).minOn f h = a := by
  induction n
  · simp at h
  · rename_i n ih
    simp only [ne_eq, replicate_eq_nil_iff] at ih
    simp +contextual [List.replicate, List.minOn_cons, ih]

/-! ### maxOn -/

protected theorem maxOn_eq_minOn {le : LE β} {dle : DecidableLE β} {xs : List α} {f : α → β} {h} :
    xs.maxOn f h = (letI := le.opposite; xs.minOn f h) :=
  (rfl)

@[simp]
protected theorem maxOn_singleton [LE β] [DecidableLE β] {x : α} {f : α → β} :
    [x].maxOn f (of_decide_eq_false rfl) = x := by
  simp [List.maxOn]

protected theorem maxOn_cons
    [LE β] [DecidableLE β] [IsLinearPreorder β] {x : α} {xs : List α} {f : α → β} :
    (x :: xs).maxOn f (by exact of_decide_eq_false rfl) =
      if h : xs = [] then x else maxOn f x (xs.maxOn f h) := by
  simp only [maxOn_eq_minOn]
  letI : LE β := (inferInstanceAs (LE β)).opposite
  exact List.minOn_cons (f := f)

protected theorem min_eq_max {min : Min α} {xs : List α} {h} :
    xs.min h = (letI := min.oppositeMax; xs.max h) := by
  simp only [List.min, List.max]
  rw [Min.oppositeMax_def]
  simp; try rfl

protected theorem max_eq_min {max : Max α} {xs : List α} {h} :
    xs.max h = (letI := max.oppositeMin; xs.min h) := by
  simp only [List.min, List.max]
  rw [Max.oppositeMin_def]
  simp; try rfl

protected theorem max?_eq_min? {max : Max α} {xs : List α} :
    xs.max? = (letI := max.oppositeMin; xs.min?) := by
  simp only [List.min?, List.max?]
  rw [Max.oppositeMin_def]
  first | simp | rfl

@[simp]
protected theorem maxOn_id [Max α] [LE α] [DecidableLE α] [LawfulOrderLeftLeaningMax α]
    {xs : List α} (h : xs ≠ []) :
    xs.maxOn id h = xs.max h := by
  simp only [List.maxOn_eq_minOn]
  letI : LE α := (inferInstanceAs (LE α)).opposite
  letI : Min α := (inferInstanceAs (Max α)).oppositeMin
  simpa only [List.max_eq_min] using List.minOn_id h

@[simp]
protected theorem maxOn_mem [LE β] [DecidableLE β] {xs : List α}
    {f : α → β} {h : xs ≠ []} : xs.maxOn f h ∈ xs :=
  letI : LE β := (inferInstanceAs (LE β)).opposite
  List.minOn_mem (f := f)

protected theorem le_apply_maxOn_of_mem [LE β] [DecidableLE β] [IsLinearPreorder β]
    {xs : List α} {f : α → β} {y : α} (hx : y ∈ xs) :
    f y ≤ f (xs.maxOn f (List.ne_nil_of_mem hx)) := by
  rw [List.maxOn_eq_minOn]
  letI : LE β := (inferInstanceAs (LE β)).opposite
  simpa [LE.le_opposite_iff] using List.apply_minOn_le_of_mem (f := f) hx

protected theorem apply_maxOn_le_iff [LE β] [DecidableLE β] [IsLinearPreorder β] {xs : List α}
    {f : α → β} (h : xs ≠ []) {b : β} :
    f (xs.maxOn f h) ≤ b ↔ ∀ x ∈ xs, f x ≤ b := by
  rw [List.maxOn_eq_minOn]
  letI : LE β := (inferInstanceAs (LE β)).opposite
  simpa [LE.le_opposite_iff] using List.le_apply_minOn_iff (f := f) h

protected theorem le_apply_maxOn_iff [LE β] [DecidableLE β] [IsLinearPreorder β] {xs : List α}
    {f : α → β} (h : xs ≠ []) {b : β} :
    b ≤ f (xs.maxOn f h) ↔ ∃ x ∈ xs, b ≤ f x := by
  rw [List.maxOn_eq_minOn]
  letI : LE β := (inferInstanceAs (LE β)).opposite
  simpa [LE.le_opposite_iff] using List.apply_minOn_le_iff (f := f) h

protected theorem apply_maxOn_lt_iff
     [LE β] [DecidableLE β] [LT β] [IsLinearPreorder β] [LawfulOrderLT β]
    {xs : List α} {f : α → β} (h : xs ≠ []) {b : β} :
    f (xs.maxOn f h) < b ↔ ∀ x ∈ xs, f x < b := by
  letI : LE β := (inferInstanceAs (LE β)).opposite
  letI : LT β := (inferInstanceAs (LT β)).opposite
  simpa [LT.lt_opposite_iff] using List.lt_apply_minOn_iff (f := f) h

protected theorem lt_apply_maxOn_iff
     [LE β] [DecidableLE β] [LT β] [IsLinearPreorder β] [LawfulOrderLT β]
    {xs : List α} {f : α → β} (h : xs ≠ []) {b : β} :
    b < f (xs.maxOn f h) ↔ ∃ x ∈ xs, b < f x := by
  letI : LE β := (inferInstanceAs (LE β)).opposite
  letI : LT β := (inferInstanceAs (LT β)).opposite
  simpa [LT.lt_opposite_iff] using List.apply_minOn_lt_iff (f := f) h

protected theorem apply_maxOn_le_apply_maxOn_of_subset [LE β] [DecidableLE β]
    [IsLinearPreorder β] {xs ys : List α} {f : α → β} (hxs : ys ⊆ xs) (hys : ys ≠ []) :
    haveI : xs ≠ [] := by intro h; rw [h] at hxs; simp_all [subset_nil]
    f (ys.maxOn f hys) ≤ f (xs.maxOn f this) := by
  rw [List.maxOn_eq_minOn]
  letI : LE β := (inferInstanceAs (LE β)).opposite
  simpa [LE.le_opposite_iff] using List.apply_minOn_le_apply_minOn_of_subset (f := f) hxs hys

protected theorem apply_maxOn_take_le [LE β] [DecidableLE β] [IsLinearPreorder β]
    {xs : List α} {f : α → β} {i : Nat} (h : xs.take i ≠ []) :
    f ((xs.take i).maxOn f h) ≤ f (xs.maxOn f (List.ne_nil_of_take_ne_nil h)) := by
  rw [List.maxOn_eq_minOn]
  letI : LE β := (inferInstanceAs (LE β)).opposite
  simpa [LE.le_opposite_iff] using List.le_apply_minOn_take (f := f) h

protected theorem le_apply_maxOn_append_left [LE β] [DecidableLE β] [IsLinearPreorder β]
    {xs ys : List α} {f : α → β} (h : xs ≠ []) :
    f (xs.maxOn f h) ≤
      f ((xs ++ ys).maxOn f (append_ne_nil_of_left_ne_nil h ys)) := by
  rw [List.maxOn_eq_minOn]
  letI : LE β := (inferInstanceAs (LE β)).opposite
  simpa [LE.le_opposite_iff] using List.apply_minOn_append_le_left (f := f) h

protected theorem le_apply_maxOn_append_right [LE β] [DecidableLE β] [IsLinearPreorder β]
    {xs ys : List α} {f : α → β} (h : ys ≠ []) :
    f (ys.maxOn f h) ≤
      f ((xs ++ ys).maxOn f (append_ne_nil_of_right_ne_nil xs h)) := by
  rw [List.maxOn_eq_minOn]
  letI : LE β := (inferInstanceAs (LE β)).opposite
  simpa [LE.le_opposite_iff] using List.apply_minOn_append_le_right (f := f) h

@[simp]
protected theorem maxOn_append [LE β] [DecidableLE β] [IsLinearPreorder β] {xs ys : List α}
    {f : α → β} (hxs : xs ≠ []) (hys : ys ≠ []) :
    (xs ++ ys).maxOn f (by simp [hxs]) = maxOn f (xs.maxOn f hxs) (ys.maxOn f hys) := by
  simp only [List.maxOn_eq_minOn, maxOn_eq_minOn]
  letI : LE β := (inferInstanceAs (LE β)).opposite
  simpa [LE.le_opposite_iff] using List.minOn_append (f := f) hxs hys

protected theorem maxOn_eq_head [LE β] [DecidableLE β] [IsLinearPreorder β] {xs : List α}
    {f : α → β} (h : xs ≠ []) (h' : ∀ x ∈ xs, f x ≤ f (xs.head h)) :
    xs.maxOn f h = xs.head h := by
  rw [List.maxOn_eq_minOn]
  letI : LE β := (inferInstanceAs (LE β)).opposite
  simpa [LE.le_opposite_iff] using List.minOn_eq_head (f := f) h (by simpa [LE.le_opposite_iff] using h')

protected theorem max_map
    [LE β] [DecidableLE β] [Max β] [IsLinearPreorder β] [LawfulOrderLeftLeaningMax β] {xs : List α}
    {f : α → β} (h : xs ≠ []) : (xs.map f).max (by simpa) = f (xs.maxOn f h) := by
  letI : LE β := (inferInstanceAs (LE β)).opposite
  letI : Min β := (inferInstanceAs (Max β)).oppositeMin
  simpa [List.max_eq_min] using List.min_map (f := f) h

@[simp]
protected theorem maxOn_replicate [LE β] [DecidableLE β] [IsLinearPreorder β]
    {n : Nat} {a : α} {f : α → β} (h : replicate n a ≠ []) :
    (replicate n a).maxOn f h = a :=
  letI : LE β := (inferInstanceAs (LE β)).opposite
  List.minOn_replicate (f := f) h

/-! ### minOn? -/

/-- {lit}`List.minOn?` returns {name}`none` when applied to an empty list. -/
@[simp]
protected theorem minOn?_nil [LE β] [DecidableLE β] {f : α → β} :
    ([] : List α).minOn? f = none := by
  simp [List.minOn?]

protected theorem minOn?_cons_eq_some_minOn
    [LE β] [DecidableLE β] {f : α → β} {x : α} {xs : List α} :
    (x :: xs).minOn? f = some ((x :: xs).minOn f (fun h => nomatch h)) := by
  simp [List.minOn?, List.minOn]

protected theorem minOn?_cons
    [LE β] [DecidableLE β] [IsLinearPreorder β] {f : α → β} {x : α} {xs : List α} :
    (x :: xs).minOn? f = some ((xs.minOn? f).elim x (minOn f x)) := by
  simp only [List.minOn?]
  split <;> simp [foldl_assoc]

@[simp]
protected theorem minOn?_singleton [LE β] [DecidableLE β] {x : α} {f : α → β} :
    [x].minOn? f = some x := by
  simp [List.minOn?_cons_eq_some_minOn]

@[simp]
protected theorem minOn?_id [Min α] [LE α] [DecidableLE α] [LawfulOrderLeftLeaningMin α]
    {xs : List α} : xs.minOn? id = xs.min? := by
  cases xs
  · simp
  · simp only [List.minOn?_cons_eq_some_minOn, List.minOn_id, List.min?_eq_some_min (List.cons_ne_nil _ _)]

protected theorem minOn?_eq_if
    [LE β] [DecidableLE β] [IsLinearPreorder β] {f : α → β} {xs : List α} :
  xs.minOn? f =
    if h : xs ≠ [] then
      some (xs.minOn f h)
    else
      none := by
  fun_cases xs.minOn? f <;> simp [List.minOn]

@[simp]
protected theorem isSome_minOn?_iff [LE β] [DecidableLE β] {f : α → β} {xs : List α} :
    (xs.minOn? f).isSome ↔ xs ≠ [] := by
  fun_cases xs.minOn? f <;> simp

protected theorem minOn_eq_get_minOn? [LE β] [DecidableLE β] {f : α → β} {xs : List α}
    (h : xs ≠ []) : xs.minOn f h = (xs.minOn? f).get (List.isSome_minOn?_iff.mpr h) := by
  fun_cases xs.minOn? f
  · contradiction
  · simp [List.minOn?, List.minOn]

protected theorem minOn?_eq_some_minOn [LE β] [DecidableLE β] {f : α → β} {xs : List α}
    (h : xs ≠ []) : xs.minOn? f = some (xs.minOn f h) := by
  simp [List.minOn_eq_get_minOn? h]

@[simp]
protected theorem get_minOn? [LE β] [DecidableLE β] {f : α → β} {xs : List α}
    (h : xs ≠ []) : (xs.minOn? f).get (List.isSome_minOn?_iff.mpr h) = xs.minOn f h := by
  rw [List.minOn_eq_get_minOn?]

protected theorem minOn_eq_of_minOn?_eq_some
    [LE β] [DecidableLE β] {f : α → β} {xs : List α} {x : α} (h : xs.minOn? f = some x) :
    xs.minOn f (List.isSome_minOn?_iff.mp (Option.isSome_of_eq_some h)) = x := by
  have h' := List.isSome_minOn?_iff.mp (Option.isSome_of_eq_some h)
  rwa [List.minOn?_eq_some_minOn h', Option.some.injEq] at h

protected theorem isSome_minOn?_of_mem
    [LE β] [DecidableLE β] {f : α → β} {xs : List α} {x : α} (h : x ∈ xs) :
    (xs.minOn? f).isSome := by
  apply List.isSome_minOn?_iff.mpr
  exact ne_nil_of_mem h

protected theorem apply_get_minOn?_le_of_mem
    [LE β] [DecidableLE β] [IsLinearPreorder β] {f : α → β} {xs : List α} {x : α} (h : x ∈ xs) :
    f ((xs.minOn? f).get (List.isSome_minOn?_of_mem h)) ≤ f x := by
  rw [List.get_minOn? (ne_nil_of_mem h)]
  apply List.apply_minOn_le_of_mem h

protected theorem minOn?_mem [LE β] [DecidableLE β] {xs : List α}
    {f : α → β} (h : xs.minOn? f = some a) : a ∈ xs := by
  rw [← List.minOn_eq_of_minOn?_eq_some h]
  apply List.minOn_mem

protected theorem minOn?_replicate [LE β] [DecidableLE β] [IsLinearPreorder β]
    {n : Nat} {a : α} {f : α → β} :
    (replicate n a).minOn? f = if n = 0 then none else some a := by
  split
  · simp [*]
  · rw [List.minOn?_eq_some_minOn, List.minOn_replicate]
    simp [*]

@[simp]
protected theorem minOn?_replicate_of_pos [LE β] [DecidableLE β] [IsLinearPreorder β]
    {n : Nat} {a : α} {f : α → β} (h : 0 < n) :
    (replicate n a).minOn? f = some a := by
  simp [List.minOn?_replicate, show n ≠ 0 from Nat.ne_zero_of_lt h]

@[simp]
protected theorem minOn?_append [LE β] [DecidableLE β] [IsLinearPreorder β]
    (xs ys : List α) (f : α → β) :
    (xs ++ ys).minOn? f =
      (xs.minOn? f).merge (_root_.minOn f) (ys.minOn? f) := by
  by_cases xs = [] <;> by_cases ys = [] <;> simp [*, List.minOn?_eq_if, List.minOn_append]

/-! ### maxOn? -/

protected theorem maxOn?_eq_minOn? {le : LE β} {dle : DecidableLE β} {xs : List α} {f : α → β} :
    xs.maxOn? f = (letI := le.opposite; xs.minOn? f) :=
  (rfl)

@[simp]
protected theorem maxOn?_nil [LE β] [DecidableLE β] {f : α → β} :
    ([] : List α).maxOn? f = none :=
  List.minOn?_nil (f := f)

protected theorem maxOn?_cons_eq_some_maxOn
    [LE β] [DecidableLE β] {f : α → β} {x : α} {xs : List α} :
    (x :: xs).maxOn? f = some ((x :: xs).maxOn f (fun h => nomatch h)) :=
  letI : LE β := (inferInstanceAs (LE β)).opposite
  List.minOn?_cons_eq_some_minOn

protected theorem maxOn?_cons
    [LE β] [DecidableLE β] [IsLinearPreorder β] {f : α → β} {x : α} {xs : List α} :
    (x :: xs).maxOn? f = some ((xs.maxOn? f).elim x (maxOn f x)) := by
  have : maxOn f x = (letI : LE β := LE.opposite inferInstance; minOn f x) := by
    ext; simp only [maxOn_eq_minOn]
  simp only [List.maxOn?_eq_minOn?, this]
  letI : LE β := (inferInstanceAs (LE β)).opposite
  exact List.minOn?_cons

@[simp]
protected theorem maxOn?_singleton [LE β] [DecidableLE β] {x : α} {f : α → β} :
    [x].maxOn? f = some x :=
  List.minOn?_singleton (f := f)

@[simp]
protected theorem maxOn?_id [Max α] [LE α] [DecidableLE α] [LawfulOrderLeftLeaningMax α]
    {xs : List α} : xs.maxOn? id = xs.max? := by
  letI : LE α := (inferInstanceAs (LE α)).opposite
  letI : Min α := (inferInstanceAs (Max α)).oppositeMin
  simpa only [List.maxOn?_eq_minOn?, List.max?_eq_min?] using List.minOn?_id (α := α)

protected theorem maxOn?_eq_if
    [LE β] [DecidableLE β] [IsLinearPreorder β] {f : α → β} {xs : List α} :
  xs.maxOn? f =
    if h : xs ≠ [] then
      some (xs.maxOn f h)
    else
      none :=
  letI : LE β := (inferInstanceAs (LE β)).opposite
  List.minOn?_eq_if

@[simp]
protected theorem isSome_maxOn?_iff [LE β] [DecidableLE β] {f : α → β} {xs : List α} :
    (xs.maxOn? f).isSome ↔ xs ≠ [] := by
  fun_cases xs.maxOn? f <;> simp

protected theorem maxOn_eq_get_maxOn? [LE β] [DecidableLE β] {f : α → β} {xs : List α}
    (h : xs ≠ []) : xs.maxOn f h = (xs.maxOn? f).get (List.isSome_maxOn?_iff.mpr h) :=
  letI : LE β := (inferInstanceAs (LE β)).opposite
  List.minOn_eq_get_minOn? (f := f) h

protected theorem maxOn?_eq_some_maxOn [LE β] [DecidableLE β] {f : α → β} {xs : List α}
    (h : xs ≠ []) : xs.maxOn? f = some (xs.maxOn f h) :=
  letI : LE β := (inferInstanceAs (LE β)).opposite
  List.minOn?_eq_some_minOn (f := f) h

@[simp]
protected theorem get_maxOn? [LE β] [DecidableLE β] {f : α → β} {xs : List α}
    (h : xs ≠ []) : (xs.maxOn? f).get (List.isSome_maxOn?_iff.mpr h) = xs.maxOn f h :=
  letI : LE β := (inferInstanceAs (LE β)).opposite
  List.get_minOn? (f := f) h

protected theorem maxOn_eq_of_maxOn?_eq_some
    [LE β] [DecidableLE β] {f : α → β} {xs : List α} {x : α} (h : xs.maxOn? f = some x) :
    xs.maxOn f (List.isSome_maxOn?_iff.mp (Option.isSome_of_eq_some h)) = x :=
  letI : LE β := (inferInstanceAs (LE β)).opposite
  List.minOn_eq_of_minOn?_eq_some (f := f) h

protected theorem isSome_maxOn?_of_mem
    [LE β] [DecidableLE β] {f : α → β} {xs : List α} {x : α} (h : x ∈ xs) :
    (xs.maxOn? f).isSome :=
  letI : LE β := (inferInstanceAs (LE β)).opposite
  List.isSome_minOn?_of_mem (f := f) h

protected theorem le_apply_get_maxOn?_of_mem
    [LE β] [DecidableLE β] [IsLinearPreorder β] {f : α → β} {xs : List α} {x : α} (h : x ∈ xs) :
    f x ≤ f ((xs.maxOn? f).get (List.isSome_maxOn?_of_mem h)) := by
  simp only [List.maxOn?_eq_minOn?]
  letI : LE β := (inferInstanceAs (LE β)).opposite
  simpa [LE.le_opposite_iff] using List.apply_get_minOn?_le_of_mem (f := f) h

protected theorem maxOn?_mem [LE β] [DecidableLE β] {xs : List α}
    {f : α → β} (h : xs.maxOn? f = some a) : a ∈ xs :=
  letI : LE β := (inferInstanceAs (LE β)).opposite
  List.minOn?_mem (f := f) h

protected theorem maxOn?_replicate [LE β] [DecidableLE β] [IsLinearPreorder β]
    {n : Nat} {a : α} {f : α → β} :
    (replicate n a).maxOn? f = if n = 0 then none else some a :=
  letI : LE β := (inferInstanceAs (LE β)).opposite
  List.minOn?_replicate

@[simp]
protected theorem maxOn?_replicate_of_pos [LE β] [DecidableLE β] [IsLinearPreorder β]
    {n : Nat} {a : α} {f : α → β} (h : 0 < n) :
    (replicate n a).maxOn? f = some a :=
  letI : LE β := (inferInstanceAs (LE β)).opposite
  List.minOn?_replicate_of_pos (f := f) h

@[simp]
protected theorem maxOn?_append [LE β] [DecidableLE β] [IsLinearPreorder β]
    (xs ys : List α) (f : α → β) : (xs ++ ys).maxOn? f =
      (xs.maxOn? f).merge (_root_.maxOn f) (ys.maxOn? f) := by
  have : maxOn f = (letI : LE β := LE.opposite inferInstance; minOn f) := by
    ext; simp only [maxOn_eq_minOn]
  simp only [List.maxOn?_eq_minOn?, this]
  letI : LE β := (inferInstanceAs (LE β)).opposite
  exact List.minOn?_append xs ys f

end List
