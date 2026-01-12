/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Order.MinMaxOn
import all Init.Data.Order.MinMaxOn
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

namespace List

/--
Returns an element of the non-empty list {name}`l` that minimizes {name}`f`. If {given}`x, y` are
such that {lean}`f x = f y`, it returns whichever comes first in the list.
-/
@[inline, suggest_for List.argmin]
protected def minOn [LE β] [DecidableLE β] (f : α → β) (l : List α) (h : l ≠ []) : α :=
  match l with
  | x :: xs => xs.foldl (init := x) (minOn f)

/--
Returns an element of the non-empty list {name}`l` that maximizes {name}`f`. If {given}`x, y` are
such that {lean}`f x = f y`, it returns whichever comes first in the list.
-/
@[inline, suggest_for List.argmax]
protected def maxOn [i : LE β] [DecidableLE β] (f : α → β) (l : List α) (h : l ≠ []) : α :=
  letI : LE β := i.opposite
  l.minOn f h

/--
Returns an element of {name}`l` that minimizes {name}`f`. If {given}`x, y` are such that
{lean}`f x = f y`, it returns whichever comes first in the list. Returns {name}`none` if the list is
empty.
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
-/
@[inline, suggest_for List.argmax? List.argmax] -- Mathlib's `List.argmax` returns an `Option α`
protected def maxOn? [LE β] [DecidableLE β] (f : α → β) (l : List α) : Option α :=
  match l with
  | [] => none
  | x :: xs => some (xs.foldl (init := x) (maxOn f))

/-! ### minOn -/

@[simp, grind =]
theorem minOn_singleton [LE β] [DecidableLE β] {x : α} {f : α → β} :
    [x].minOn f (of_decide_eq_false rfl) = x := by
  simp [List.minOn]

theorem minOn_cons
    [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {x : α} {xs : List α} {f : α → β} :
    (x :: xs).minOn f (by exact of_decide_eq_false rfl) =
      if h : xs = [] then x else minOn f x (xs.minOn f h) := by
  simp only [List.minOn]
  match xs with
  | [] => simp
  | y :: xs => simp [foldl_assoc]

@[grind .]
theorem minOn_mem [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {xs : List α}
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

@[grind =>]
theorem apply_minOn_le_of_mem [LE β] [DecidableLE β] [Std.IsLinearPreorder β]
    {xs : List α} {f : α → β} {y : α} (hx : y ∈ xs) :
    f (xs.minOn f (List.ne_nil_of_mem hx)) ≤ f y := by
  have h : xs ≠ [] := List.ne_nil_of_mem hx
  simp only [List.minOn]
  match xs with
  | x :: xs =>
    fun_induction xs.foldl (init := x) (_root_.minOn f) generalizing y
    · simp only [mem_cons] at hx
      simp_all [Std.le_refl _]
    · rename_i x y _ ih
      simp at ih ⊢
      rcases mem_cons.mp hx with rfl | hx
      · exact Std.le_trans ih.1 apply_minOn_le_left
      · rcases mem_cons.mp hx with rfl | hx
        · exact Std.le_trans ih.1 apply_minOn_le_right
        · apply ih.2
          assumption

protected theorem le_apply_minOn_iff [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {xs : List α}
    {f : α → β} (h : xs ≠ []) {b : β} :
    b ≤ f (xs.minOn f h) ↔ ∀ x ∈ xs, b ≤ f x := by
  match xs with
  | x :: xs =>
    rw [List.minOn]
    induction xs generalizing x
    · simp
    · rw [foldl_cons, foldl_assoc, le_apply_minOn_iff]
      simp_all

protected theorem apply_minOn_le_iff [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {xs : List α}
    {f : α → β} (h : xs ≠ []) {b : β} :
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
    exact Std.le_trans (apply_minOn_le_of_mem hm) hx

protected theorem lt_apply_minOn_iff
     [LE β] [DecidableLE β] [LT β] [Std.IsLinearPreorder β] [Std.LawfulOrderLT β]
    {xs : List α} {f : α → β} (h : xs ≠ []) {b : β} :
    b < f (xs.minOn f h) ↔ ∀ x ∈ xs, b < f x := by
  simpa [Std.not_le] using not_congr <| xs.apply_minOn_le_iff (f := f) h (b := b)

protected theorem apply_minOn_lt_iff
     [LE β] [DecidableLE β] [LT β] [Std.IsLinearPreorder β] [Std.LawfulOrderLT β]
    {xs : List α} {f : α → β} (h : xs ≠ []) {b : β} :
    f (xs.minOn f h) < b ↔ ∃ x ∈ xs, f x < b := by
  simpa [Std.not_le] using not_congr <| xs.le_apply_minOn_iff (f := f) h (b := b)

theorem apply_minOn_le_apply_minOn_of_subset [LE β] [DecidableLE β] [Std.IsLinearPreorder β]
    {xs ys : List α} {f : α → β} (hxs : ys ⊆ xs) (hys : ys ≠ []) :
    haveI : xs ≠ [] := by intro h; rw [h] at hxs; simp_all [subset_nil]
    f (xs.minOn f this) ≤ f (ys.minOn f hys) := by
  rw [List.le_apply_minOn_iff]
  intro x hx
  exact apply_minOn_le_of_mem (hxs hx)

theorem le_apply_minOn_take [LE β] [DecidableLE β] [Std.IsLinearPreorder β]
    {xs : List α} {f : α → β} {i : Nat} (h : xs.take i ≠ []) :
    f (xs.minOn f (List.ne_nil_of_take_ne_nil h)) ≤ f ((xs.take i).minOn f h) := by
  apply apply_minOn_le_apply_minOn_of_subset
  apply take_subset

theorem apply_minOn_append_le_left [LE β] [DecidableLE β] [Std.IsLinearPreorder β]
    {xs ys : List α} {f : α → β} (h : xs ≠ []) :
    f ((xs ++ ys).minOn f (append_ne_nil_of_left_ne_nil h ys)) ≤
      f (xs.minOn f h) := by
  apply apply_minOn_le_apply_minOn_of_subset
  apply subset_append_left

theorem apply_minOn_append_le_right [LE β] [DecidableLE β] [Std.IsLinearPreorder β]
    {xs ys : List α} {f : α → β} (h : ys ≠ []) :
    f ((xs ++ ys).minOn f (append_ne_nil_of_right_ne_nil xs h)) ≤
      f (ys.minOn f h) := by
  apply apply_minOn_le_apply_minOn_of_subset
  apply subset_append_right

@[grind =]
theorem minOn_append [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {xs ys : List α}
    {f : α → β} (hxs : xs ≠ []) (hys : ys ≠ []) :
    (xs ++ ys).minOn f (by simp [hxs]) = minOn f (xs.minOn f hxs) (ys.minOn f hys) := by
  match xs, ys with
  | x :: xs, y :: ys => simp [List.minOn, foldl_assoc]

theorem minOn_eq_head [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {xs : List α}
    {f : α → β} (h : xs ≠ []) (h' : ∀ x ∈ xs, f (xs.head h) ≤ f x) :
    xs.minOn f h = xs.head h := by
  match xs with
  | x :: xs =>
    simp only [List.minOn]
    induction xs
    · simp
    · simp only [foldl_cons, head_cons]
      rw [minOn_eq_left] <;> simp_all

protected theorem min_map
    [LE β] [DecidableLE β] [Min β] [Std.IsLinearPreorder β] [Std.LawfulOrderLeftLeaningMin β] {xs : List α} {f : α → β} (h : xs ≠ []) :
    (xs.map f).min (by simpa) = f (xs.minOn f h) := by
  match xs with
  | x :: xs =>
    simp only [List.minOn, map_cons, List.min, foldl_map]
    rw [foldl_hom]
    simp [min_apply]

@[simp]
theorem minOn_replicate [LE β] [DecidableLE β] [Std.IsLinearPreorder β]
    {n : Nat} {a : α} {f : α → β} (h : replicate n a ≠ []) :
    (replicate n a).minOn f h = a := by
  induction n
  · simp at h
  · rename_i n ih
    simp only [ne_eq, replicate_eq_nil_iff] at ih
    simp +contextual [List.replicate, List.minOn_cons, ih]

/-! ### maxOn -/

@[simp, grind =]
theorem maxOn_singleton [LE β] [DecidableLE β] {x : α} {f : α → β} :
    [x].maxOn f (of_decide_eq_false rfl) = x := by
  simp [List.maxOn]

theorem maxOn_cons
    [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {x : α} {xs : List α} {f : α → β} :
    (x :: xs).maxOn f (by exact of_decide_eq_false rfl) =
      if h : xs = [] then x else maxOn f x (xs.maxOn f h) :=
  letI : LE β := (inferInstanceAs (LE β)).opposite
  minOn_cons (f := f)

@[grind .]
theorem maxOn_mem [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {xs : List α}
    {f : α → β} {h : xs ≠ []} : xs.maxOn f h ∈ xs :=
  letI : LE β := (inferInstanceAs (LE β)).opposite
  minOn_mem (f := f)

@[grind =>]
theorem le_apply_maxOn_of_mem [LE β] [DecidableLE β] [Std.IsLinearPreorder β]
    {xs : List α} {f : α → β} {y : α} (hx : y ∈ xs) :
    f y ≤ f (xs.maxOn f (List.ne_nil_of_mem hx)) :=
  letI : LE β := (inferInstanceAs (LE β)).opposite
  apply_minOn_le_of_mem (f := f) hx

protected theorem apply_maxOn_le_iff [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {xs : List α}
    {f : α → β} (h : xs ≠ []) {b : β} :
    f (xs.maxOn f h) ≤ b ↔ ∀ x ∈ xs, f x ≤ b :=
  letI : LE β := (inferInstanceAs (LE β)).opposite
  List.le_apply_minOn_iff (f := f) h

protected theorem le_apply_maxOn_iff [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {xs : List α}
    {f : α → β} (h : xs ≠ []) {b : β} :
    b ≤ f (xs.maxOn f h) ↔ ∃ x ∈ xs, b ≤ f x :=
  letI : LE β := (inferInstanceAs (LE β)).opposite
  List.apply_minOn_le_iff (f := f) h

protected theorem apply_maxOn_lt_iff
     [LE β] [DecidableLE β] [LT β] [Std.IsLinearPreorder β] [Std.LawfulOrderLT β]
    {xs : List α} {f : α → β} (h : xs ≠ []) {b : β} :
    f (xs.maxOn f h) < b ↔ ∀ x ∈ xs, f x < b :=
  letI : LE β := (inferInstanceAs (LE β)).opposite
  letI : LT β := (inferInstanceAs (LT β)).opposite
  List.lt_apply_minOn_iff (f := f) h

protected theorem lt_apply_maxOn_iff
     [LE β] [DecidableLE β] [LT β] [Std.IsLinearPreorder β] [Std.LawfulOrderLT β]
    {xs : List α} {f : α → β} (h : xs ≠ []) {b : β} :
    b < f (xs.maxOn f h) ↔ ∃ x ∈ xs, b < f x :=
  letI : LE β := (inferInstanceAs (LE β)).opposite
  letI : LT β := (inferInstanceAs (LT β)).opposite
  List.apply_minOn_lt_iff (f := f) h

theorem apply_maxOn_le_apply_maxOn_of_subset [LE β] [DecidableLE β] [Std.IsLinearPreorder β]
    {xs ys : List α} {f : α → β} (hxs : ys ⊆ xs) (hys : ys ≠ []) :
    haveI : xs ≠ [] := by intro h; rw [h] at hxs; simp_all [subset_nil]
    f (ys.maxOn f hys) ≤ f (xs.maxOn f this) :=
  letI : LE β := (inferInstanceAs (LE β)).opposite
  apply_minOn_le_apply_minOn_of_subset (f := f) hxs hys

theorem apply_maxOn_take_le [LE β] [DecidableLE β] [Std.IsLinearPreorder β]
    {xs : List α} {f : α → β} {i : Nat} (h : xs.take i ≠ []) :
    f ((xs.take i).maxOn f h) ≤ f (xs.maxOn f (List.ne_nil_of_take_ne_nil h)) :=
  letI : LE β := (inferInstanceAs (LE β)).opposite
  le_apply_minOn_take (f := f) h

@[grind =]
theorem maxOn_append [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {xs ys : List α}
    {f : α → β} (hxs : xs ≠ []) (hys : ys ≠ []) :
    (xs ++ ys).maxOn f (by simp [hxs]) = maxOn f (xs.maxOn f hxs) (ys.maxOn f hys) :=
  letI : LE β := (inferInstanceAs (LE β)).opposite
  minOn_append (f := f) hxs hys

theorem le_apply_maxOn_append_left [LE β] [DecidableLE β] [Std.IsLinearPreorder β]
    {xs ys : List α} {f : α → β} (h : xs ≠ []) :
    f (xs.maxOn f h) ≤
      f ((xs ++ ys).maxOn f (append_ne_nil_of_left_ne_nil h ys)) :=
  letI : LE β := (inferInstanceAs (LE β)).opposite
  apply_minOn_append_le_left (f := f) h

theorem le_apply_maxOn_append_right [LE β] [DecidableLE β] [Std.IsLinearPreorder β]
    {xs ys : List α} {f : α → β} (h : ys ≠ []) :
    f (ys.maxOn f h) ≤
      f ((xs ++ ys).maxOn f (append_ne_nil_of_right_ne_nil xs h)) :=
  letI : LE β := (inferInstanceAs (LE β)).opposite
  apply_minOn_append_le_right (f := f) h

theorem maxOn_eq_head [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {xs : List α}
    {f : α → β} (h : xs ≠ []) (h' : ∀ x ∈ xs, f x ≤ f (xs.head h)) :
    xs.maxOn f h = xs.head h :=
  letI : LE β := (inferInstanceAs (LE β)).opposite
  minOn_eq_head (f := f) h h'

protected theorem max_map
    [LE β] [DecidableLE β] [Max β] [Std.IsLinearPreorder β] [Std.LawfulOrderLeftLeaningMax β] {xs : List α} {f : α → β} (h : xs ≠ []) :
    (xs.map f).max (by simpa) = f (xs.maxOn f h) :=
  letI : LE β := (inferInstanceAs (LE β)).opposite
  letI : Min β := (inferInstanceAs (Max β)).oppositeMin
  List.min_map (f := f) h

@[simp]
theorem maxOn_replicate [LE β] [DecidableLE β] [Std.IsLinearPreorder β]
    {n : Nat} {a : α} {f : α → β} (h : replicate n a ≠ []) :
    (replicate n a).maxOn f h = a :=
  letI : LE β := (inferInstanceAs (LE β)).opposite
  minOn_replicate (f := f) h

/-! ### minOn? -/

/-- {lit}`List.minOn?` returns {name}`none` when applied to an empty list. -/
@[simp, grind =]
theorem minOn?_nil [LE β] [DecidableLE β] {f : α → β} :
    ([] : List α).minOn? f = none := by
  simp [List.minOn?]

theorem minOn?_cons_eq_some_minOn
    [LE β] [DecidableLE β] {f : α → β} {x : α} {xs : List α} :
    (x :: xs).minOn? f = some ((x :: xs).minOn f (fun h => nomatch h)) := by
  simp [List.minOn?, List.minOn]

@[simp, grind =]
theorem minOn?_singleton [LE β] [DecidableLE β] {x : α} {f : α → β} :
    [x].minOn? f = some x := by
  simp [minOn?_cons_eq_some_minOn]

@[grind =]
theorem minOn?_cons
    [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {f : α → β} {x : α} {xs : List α} :
    (x :: xs).minOn? f = some ((xs.minOn? f).elim x (minOn f x)) := by
  simp only [List.minOn?]
  split <;> simp [foldl_assoc]

theorem minOn?_eq_if
    [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {f : α → β} {xs : List α} :
  xs.minOn? f =
    if h : xs ≠ [] then
      some (xs.minOn f h)
    else
      none := by
  fun_cases xs.minOn? f <;> simp [List.minOn]

theorem isSome_minOn?_of_ne_nil [LE β] [DecidableLE β] {f : α → β} {xs : List α} (h : xs ≠ []) :
    (xs.minOn? f).isSome := by
  fun_cases xs.minOn? f
  · contradiction
  · simp

theorem minOn_eq_minOn?_get [LE β] [DecidableLE β] {f : α → β} {xs : List α} (h : xs ≠ []) :
    xs.minOn f h = (xs.minOn? f).get (isSome_minOn?_of_ne_nil h) := by
  fun_cases xs.minOn? f
  · contradiction
  · simp [List.minOn?, List.minOn]

theorem minOn?_eq_some_minOn [LE β] [DecidableLE β] {f : α → β} {xs : List α} (h : xs ≠ []) :
    xs.minOn? f = some (xs.minOn f h) := by
  simp [minOn_eq_minOn?_get h]

theorem minOn?_get_eq_minOn [LE β] [DecidableLE β] {f : α → β} {xs : List α} (h : xs ≠ []) :
    (xs.minOn? f).get (isSome_minOn?_of_ne_nil h) = xs.minOn f h := by
  rw [minOn_eq_minOn?_get]

@[simp, grind =]
theorem isSome_minOn_iff_ne_nil
    [LE β] [DecidableLE β] {f : α → β} {xs : List α} :
    (xs.minOn? f).isSome ↔ xs ≠ [] := by
  fun_cases xs.minOn? f <;> simp

theorem minOn_eq_of_minOn?_eq_some
    [LE β] [DecidableLE β] {f : α → β} {xs : List α} {x : α} (h : xs.minOn? f = some x) :
    xs.minOn f (isSome_minOn_iff_ne_nil.mp (Option.isSome_of_eq_some h)) = x := by
  have h' := isSome_minOn_iff_ne_nil.mp (Option.isSome_of_eq_some h)
  rwa [minOn?_eq_some_minOn h', Option.some.injEq] at h

@[grind =>]
theorem isSome_minOn?_of_mem
    [LE β] [DecidableLE β] {f : α → β} {xs : List α} {x : α} (h : x ∈ xs) :
    (xs.minOn? f).isSome := by
  apply isSome_minOn?_of_ne_nil
  exact ne_nil_of_mem h

theorem List.apply_minOn?_get_le_of_mem
    [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {f : α → β} {xs : List α} {x : α} (h : x ∈ xs) :
    f ((xs.minOn? f).get (isSome_minOn?_of_mem h)) ≤ f x := by
  rw [minOn?_get_eq_minOn (ne_nil_of_mem h)]
  apply apply_minOn_le_of_mem h

-- The suggested patterns are not useful because all involve `IsLinearPreorder`.
grind_pattern List.apply_minOn?_get_le_of_mem => x ∈ xs, (xs.minOn? f).get _

@[grind <=]
theorem minOn?_mem [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {xs : List α} {f : α → β}
    (h : xs.minOn? f = some a) : a ∈ xs := by
  rw [← minOn_eq_of_minOn?_eq_some h]
  apply minOn_mem

theorem minOn?_replicate [LE β] [DecidableLE β] [Std.IsLinearPreorder β]
    {n : Nat} {a : α} {f : α → β} :
    (replicate n a).minOn? f = if n = 0 then none else some a := by
  split
  · simp [*]
  · rw [minOn?_eq_some_minOn, minOn_replicate]
    simp [*]

@[simp, grind =]
theorem minOn?_replicate_of_pos [LE β] [DecidableLE β] [Std.IsLinearPreorder β]
    {n : Nat} {a : α} {f : α → β} (h : 0 < n) :
    (replicate n a).minOn? f = some a := by
  simp [minOn?_replicate, show n ≠ 0 from Nat.ne_zero_of_lt h]

@[grind =]
theorem List.minOn?_append [LE β] [DecidableLE β] [Std.IsLinearPreorder β] (xs ys : List α) (f : α → β) :
    (xs ++ ys).minOn? f =
      (xs.minOn? f).merge (_root_.minOn f) (ys.minOn? f) := by
  by_cases xs = [] <;> by_cases ys = [] <;> simp [*, minOn?_eq_if, minOn_append]

/-! ### maxOn? -/

@[simp, grind =]
theorem maxOn?_nil [LE β] [DecidableLE β] {f : α → β} :
    ([] : List α).maxOn? f = none :=
  minOn?_nil (f := f)

theorem maxOn?_cons_eq_some_maxOn
    [LE β] [DecidableLE β] {f : α → β} {x : α} {xs : List α} :
    (x :: xs).maxOn? f = some ((x :: xs).maxOn f (fun h => nomatch h)) :=
  letI : LE β := (inferInstanceAs (LE β)).opposite
  minOn?_cons_eq_some_minOn

@[grind =]
theorem maxOn?_cons
    [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {f : α → β} {x : α} {xs : List α} :
    (x :: xs).maxOn? f = some ((xs.maxOn? f).elim x (maxOn f x)) :=
  letI : LE β := (inferInstanceAs (LE β)).opposite
  minOn?_cons

@[simp, grind =]
theorem maxOn?_singleton [LE β] [DecidableLE β] {x : α} {f : α → β} :
    [x].maxOn? f = some x :=
  minOn?_singleton (f := f)

theorem maxOn?_eq_if
    [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {f : α → β} {xs : List α} :
  xs.maxOn? f =
    if h : xs ≠ [] then
      some (xs.maxOn f h)
    else
      none :=
  letI : LE β := (inferInstanceAs (LE β)).opposite
  minOn?_eq_if

theorem isSome_maxOn?_of_ne_nil [LE β] [DecidableLE β] {f : α → β} {xs : List α} (h : xs ≠ []) :
    (xs.maxOn? f).isSome :=
  letI : LE β := (inferInstanceAs (LE β)).opposite
  isSome_minOn?_of_ne_nil (f := f) h

theorem maxOn_eq_maxOn?_get [LE β] [DecidableLE β] {f : α → β} {xs : List α} (h : xs ≠ []) :
    xs.maxOn f h = (xs.maxOn? f).get (isSome_maxOn?_of_ne_nil h) :=
  letI : LE β := (inferInstanceAs (LE β)).opposite
  minOn_eq_minOn?_get (f := f) h

theorem maxOn?_eq_some_maxOn [LE β] [DecidableLE β] {f : α → β} {xs : List α} (h : xs ≠ []) :
    xs.maxOn? f = some (xs.maxOn f h) :=
  letI : LE β := (inferInstanceAs (LE β)).opposite
  minOn?_eq_some_minOn (f := f) h

theorem maxOn?_get_eq_maxOn [LE β] [DecidableLE β] {f : α → β} {xs : List α} (h : xs ≠ []) :
    (xs.maxOn? f).get (isSome_maxOn?_of_ne_nil h) = xs.maxOn f h :=
  letI : LE β := (inferInstanceAs (LE β)).opposite
  minOn?_get_eq_minOn (f := f) h

@[simp, grind =]
theorem isSome_maxOn_iff_ne_nil
    [LE β] [DecidableLE β] {f : α → β} {xs : List α} :
    (xs.maxOn? f).isSome ↔ xs ≠ [] :=
  letI : LE β := (inferInstanceAs (LE β)).opposite
  isSome_minOn_iff_ne_nil

theorem maxOn_eq_of_maxOn?_eq_some
    [LE β] [DecidableLE β] {f : α → β} {xs : List α} {x : α} (h : xs.maxOn? f = some x) :
    xs.maxOn f (isSome_maxOn_iff_ne_nil.mp (Option.isSome_of_eq_some h)) = x :=
  letI : LE β := (inferInstanceAs (LE β)).opposite
  minOn_eq_of_minOn?_eq_some (f := f) h

@[grind =>]
theorem isSome_maxOn?_of_mem
    [LE β] [DecidableLE β] {f : α → β} {xs : List α} {x : α} (h : x ∈ xs) :
    (xs.maxOn? f).isSome :=
  letI : LE β := (inferInstanceAs (LE β)).opposite
  isSome_minOn?_of_mem (f := f) h

theorem le_apply_maxOn?_get_of_mem
    [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {f : α → β} {xs : List α} {x : α} (h : x ∈ xs) :
    f x ≤ f ((xs.maxOn? f).get (isSome_maxOn?_of_mem h)) :=
  letI : LE β := (inferInstanceAs (LE β)).opposite
  List.apply_minOn?_get_le_of_mem (f := f) h

-- The suggested patterns are not useful because all involve `IsLinearPreorder`.
grind_pattern List.le_apply_maxOn?_get_of_mem => x ∈ xs, (xs.maxOn? f).get _

@[grind <=]
theorem maxOn?_mem [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {xs : List α} {f : α → β}
    (h : xs.maxOn? f = some a) : a ∈ xs :=
  letI : LE β := (inferInstanceAs (LE β)).opposite
  minOn?_mem (f := f) h

theorem maxOn?_replicate [LE β] [DecidableLE β] [Std.IsLinearPreorder β]
    {n : Nat} {a : α} {f : α → β} :
    (replicate n a).maxOn? f = if n = 0 then none else some a :=
  letI : LE β := (inferInstanceAs (LE β)).opposite
  minOn?_replicate

@[simp, grind =]
theorem maxOn?_replicate_of_pos [LE β] [DecidableLE β] [Std.IsLinearPreorder β]
    {n : Nat} {a : α} {f : α → β} (h : 0 < n) :
    (replicate n a).maxOn? f = some a :=
  letI : LE β := (inferInstanceAs (LE β)).opposite
  minOn?_replicate_of_pos (f := f) h

@[grind =]
theorem List.maxOn?_append [LE β] [DecidableLE β] [Std.IsLinearPreorder β] (xs ys : List α) (f : α → β) :
    (xs ++ ys).maxOn? f =
      (xs.maxOn? f).merge (_root_.maxOn f) (ys.maxOn? f) :=
  letI : LE β := (inferInstanceAs (LE β)).opposite
  List.minOn?_append xs ys f

end List
