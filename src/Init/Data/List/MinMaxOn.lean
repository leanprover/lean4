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
protected def maxOn [LE β] [DecidableLE β] (f : α → β) (l : List α) (h : l ≠ []) : α :=
  match l with
  | x :: xs => xs.foldl (init := x) (maxOn f)

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

#check le_apply_minOn_iff

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

/--
{lean}`xs.minOn f h` comes before any other element in {name}`xs` where {name}`f` attains its
minimum.
-/
theorem minOn_left_leaning
    [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {xs : List α} {f : α → β} (h : xs ≠ []) :
    ∃ j : Fin xs.length, xs[j] = xs.minOn f h ∧
      ∀ i : Fin j, ¬ f xs[i] ≤ f (xs.minOn f h) := by
  open scoped Classical.Order in
  simp only [List.minOn, Fin.getElem_fin, Std.not_le]
  match xs with
  | x :: xs =>
    simp only
    clear h
    fun_induction xs.foldl (init := x) (_root_.minOn f)
    · exact ⟨⟨0, by simp⟩, by simp⟩
    · rename_i x y xs ih
      obtain ⟨j, ih⟩ := ih
      by_cases hj : j.val = 0
      · by_cases hm : f x ≤ f y
        · exact ⟨⟨0, by simp⟩, by
            simp only [← ih.1, hj]
            simp [minOn_eq_left hm]⟩
        · simp only [Std.not_le] at hm
          exact ⟨⟨1, by simp⟩, by
            simp only [← ih.1, hj]
            simp [minOn_eq_right_of_lt, hm]⟩
      · refine ⟨⟨j + 1, by simp⟩, ?_⟩
        obtain ⟨j, _⟩ := Nat.exists_eq_succ_of_ne_zero hj
        apply And.intro
        · simp_all
        · rintro ⟨i, hi⟩
          match i with
          | 0 | 1 =>
            refine Std.lt_of_lt_of_le (ih.2 ⟨0, by simp_all⟩) ?_
            simp [apply_minOn_le_left, apply_minOn_le_right]
          | i + 2 =>
            refine Std.lt_of_lt_of_le (ih.2 ⟨i + 1, by simp_all⟩) ?_
            simp [Std.le_refl]

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
      if h : xs = [] then x else maxOn f x (xs.maxOn f h) := by
  simp only [List.maxOn]
  match xs with
  | [] => simp
  | y :: xs => simp [foldl_assoc]

@[grind .]
theorem maxOn_mem [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {xs : List α}
    {f : α → β} {h : xs ≠ []} : xs.maxOn f h ∈ xs := by
  simp only [List.maxOn]
  match xs with
  | x :: xs =>
    fun_induction xs.foldl (init := x) (_root_.maxOn f)
    · simp
    · rename_i x y _ ih
      simp only [ne_eq, reduceCtorEq, not_false_eq_true, mem_cons, forall_const, foldl_cons] at ih ⊢
      cases ih <;> rename_i heq
      · cases maxOn_eq_or (f := f) (x := x) (y := y) <;> simp_all
      · simp [*]

@[grind =>]
theorem le_apply_maxOn_of_mem [LE β] [DecidableLE β] [Std.IsLinearPreorder β]
    {xs : List α} {f : α → β} {y : α} (hx : y ∈ xs) :
    f y ≤ f (xs.maxOn f (List.ne_nil_of_mem hx)) := by
  have h : xs ≠ [] := List.ne_nil_of_mem hx
  simp only [List.maxOn]
  match xs with
  | x :: xs =>
    fun_induction xs.foldl (init := x) (_root_.maxOn f) generalizing y
    · simp only [mem_cons] at hx
      simp_all [Std.le_refl _]
    · rename_i x y _ ih
      simp at ih ⊢
      rcases mem_cons.mp hx with rfl | hx
      · exact Std.le_trans left_le_apply_maxOn ih.1
      · rcases mem_cons.mp hx with rfl | hx
        · exact Std.le_trans right_le_apply_maxOn ih.1
        · apply ih.2
          assumption

protected theorem apply_maxOn_le_iff [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {xs : List α}
    {f : α → β} (h : xs ≠ []) {b : β} :
    f (xs.maxOn f h) ≤ b ↔ ∀ x ∈ xs, f x ≤ b := by
  match xs with
  | x :: xs =>
    rw [List.maxOn]
    induction xs generalizing x
    · simp
    · rw [foldl_cons, foldl_assoc, apply_maxOn_le_iff]
      simp_all

protected theorem le_apply_maxOn_iff [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {xs : List α}
    {f : α → β} (h : xs ≠ []) {b : β} :
    b ≤ f (xs.maxOn f h) ↔ ∃ x ∈ xs, b ≤ f x := by
  apply Iff.intro
  · intro h
    match xs with
    | x :: xs =>
      rw [List.maxOn] at h
      induction xs generalizing x
      · simpa using h
      · rename_i y ys ih _
        rw [foldl_cons] at h
        specialize ih (maxOn f x y) (by simp) h
        obtain ⟨z, hm, hle⟩ := ih
        rcases mem_cons.mp hm with rfl | hm
        · cases maxOn_eq_or (f := f) (x := x) (y := y)
          · exact ⟨x, by simp_all⟩
          · exact ⟨y, by simp_all⟩
        · exact ⟨z, by simp_all⟩
  · rintro ⟨x, hm, hx⟩
    exact Std.le_trans hx (le_apply_maxOn_of_mem hm)

protected theorem apply_maxOn_lt_iff
     [LE β] [DecidableLE β] [LT β] [Std.IsLinearPreorder β] [Std.LawfulOrderLT β]
    {xs : List α} {f : α → β} (h : xs ≠ []) {b : β} :
    f (xs.maxOn f h) < b ↔ ∀ x ∈ xs, f x < b := by
  simpa [Std.not_le] using not_congr <| xs.le_apply_maxOn_iff (f := f) h (b := b)

theorem apply_maxOn_le_apply_maxOn_of_subset [LE β] [DecidableLE β] [Std.IsLinearPreorder β]
    {xs ys : List α} {f : α → β} (hxs : ys ⊆ xs) (hys : ys ≠ []) :
    haveI : xs ≠ [] := by intro h; rw [h] at hxs; simp_all [subset_nil]
    f (ys.maxOn f hys) ≤ f (xs.maxOn f this) := by
  rw [List.apply_maxOn_le_iff]
  intro x hx
  exact le_apply_maxOn_of_mem (hxs hx)

theorem apply_maxOn_take_le [LE β] [DecidableLE β] [Std.IsLinearPreorder β]
    {xs : List α} {f : α → β} {i : Nat} (h : xs.take i ≠ []) :
    f ((xs.take i).maxOn f h) ≤ f (xs.maxOn f (List.ne_nil_of_take_ne_nil h)) := by
  apply apply_maxOn_le_apply_maxOn_of_subset
  apply take_subset

@[grind =]
theorem maxOn_append [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {xs ys : List α}
    {f : α → β} (hxs : xs ≠ []) (hys : ys ≠ []) :
    (xs ++ ys).maxOn f (by simp [hxs]) = maxOn f (xs.maxOn f hxs) (ys.maxOn f hys) := by
  match xs, ys with
  | x :: xs, y :: ys => simp [List.maxOn, foldl_assoc]

theorem maxOn_eq_head [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {xs : List α}
    {f : α → β} (h : xs ≠ []) (h' : ∀ x ∈ xs, f x ≤ f (xs.head h)) :
    xs.maxOn f h = xs.head h := by
  match xs with
  | x :: xs =>
    simp only [List.maxOn]
    induction xs
    · simp
    · simp only [foldl_cons, head_cons]
      rw [maxOn_eq_left] <;> simp_all

/--
{lean}`xs.maxOn f h` comes before any other element in {name}`xs` where {name}`f` attains its
maximum.
-/
theorem maxOn_left_leaning
    [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {xs : List α} {f : α → β} (h : xs ≠ []) :
    ∃ j : Fin xs.length, xs[j] = xs.maxOn f h ∧
      ∀ i : Fin j, ¬ f (xs.maxOn f h) ≤ f xs[i] := by
  open scoped Classical.Order in
  simp only [List.maxOn, Fin.getElem_fin, Std.not_le]
  match xs with
  | x :: xs =>
    simp only
    clear h
    fun_induction xs.foldl (init := x) (_root_.maxOn f)
    · exact ⟨⟨0, by simp⟩, by simp⟩
    · rename_i x y xs ih
      obtain ⟨j, ih⟩ := ih
      by_cases hj : j.val = 0
      · by_cases hm : f y ≤ f x
        · exact ⟨⟨0, by simp⟩, by
            simp only [← ih.1, hj]
            simp [maxOn_eq_left hm]⟩
        · simp only [Std.not_le] at hm
          exact ⟨⟨1, by simp⟩, by
            simp only [← ih.1, hj]
            simp [maxOn_eq_right_of_lt, hm]⟩
      · refine ⟨⟨j + 1, by simp⟩, ?_⟩
        obtain ⟨j, _⟩ := Nat.exists_eq_succ_of_ne_zero hj
        apply And.intro
        · simp_all
        · rintro ⟨i, hi⟩
          match i with
          | 0 | 1 =>
            refine Std.lt_of_le_of_lt ?_ (ih.2 ⟨0, by simp_all⟩)
            simp [left_le_apply_maxOn, right_le_apply_maxOn]
          | i + 2 =>
            refine Std.lt_of_le_of_lt ?_ (ih.2 ⟨i + 1, by simp_all⟩)
            simp [Std.le_refl]

protected theorem max_map
    [LE β] [DecidableLE β] [Max β] [Std.IsLinearPreorder β] [Std.LawfulOrderLeftLeaningMax β] {xs : List α} {f : α → β} (h : xs ≠ []) :
    (xs.map f).max (by simpa) = f (xs.maxOn f h) := by
  match xs with
  | x :: xs =>
    simp only [List.maxOn, map_cons, List.max, foldl_map]
    rw [foldl_hom]
    simp [max_apply]

@[simp]
theorem maxOn_replicate [LE β] [DecidableLE β] [Std.IsLinearPreorder β]
    {n : Nat} {a : α} {f : α → β} (h : replicate n a ≠ []) :
    (replicate n a).maxOn f h = a := by
  induction n
  · simp at h
  · rename_i n ih
    simp only [ne_eq, replicate_eq_nil_iff] at ih
    simp +contextual [List.replicate, List.maxOn_cons, ih]

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

theorem List.minOn?_left_leaning [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {xs : List α} {f : α → β} {x : α}
    (hx : xs.minOn? f = some x) :
    ∃ j : Fin xs.length, xs[j] = x ∧ ∀ i : Fin j, ¬ f xs[i] ≤ f x := by
  rw [← minOn_eq_of_minOn?_eq_some hx]
  apply List.minOn_left_leaning

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
    ([] : List α).maxOn? f = none := by
  simp [List.maxOn?]

theorem maxOn?_cons_eq_some_maxOn
    [LE β] [DecidableLE β] {f : α → β} {x : α} {xs : List α} :
    (x :: xs).maxOn? f = some ((x :: xs).maxOn f (fun h => nomatch h)) := by
  simp [List.maxOn?, List.maxOn]

@[grind =]
theorem maxOn?_cons
    [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {f : α → β} {x : α} {xs : List α} :
    (x :: xs).maxOn? f = some ((xs.maxOn? f).elim x (maxOn f x)) := by
  simp only [List.maxOn?]
  split <;> simp [foldl_assoc]

@[simp, grind =]
theorem maxOn?_singleton [LE β] [DecidableLE β] {x : α} {f : α → β} :
    [x].maxOn? f = some x := by
  simp [maxOn?_cons_eq_some_maxOn]

theorem maxOn?_eq_if
    [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {f : α → β} {xs : List α} :
  xs.maxOn? f =
    if h : xs ≠ [] then
      some (xs.maxOn f h)
    else
      none := by
  fun_cases xs.maxOn? f <;> simp [List.maxOn]

theorem isSome_maxOn?_of_ne_nil [LE β] [DecidableLE β] {f : α → β} {xs : List α} (h : xs ≠ []) :
    (xs.maxOn? f).isSome := by
  fun_cases xs.maxOn? f
  · contradiction
  · simp

theorem maxOn_eq_maxOn?_get [LE β] [DecidableLE β] {f : α → β} {xs : List α} (h : xs ≠ []) :
    xs.maxOn f h = (xs.maxOn? f).get (isSome_maxOn?_of_ne_nil h) := by
  fun_cases xs.maxOn? f
  · contradiction
  · simp [List.maxOn?, List.maxOn]

theorem maxOn?_eq_some_maxOn [LE β] [DecidableLE β] {f : α → β} {xs : List α} (h : xs ≠ []) :
    xs.maxOn? f = some (xs.maxOn f h) := by
  simp [maxOn_eq_maxOn?_get h]

theorem maxOn?_get_eq_maxOn [LE β] [DecidableLE β] {f : α → β} {xs : List α} (h : xs ≠ []) :
    (xs.maxOn? f).get (isSome_maxOn?_of_ne_nil h) = xs.maxOn f h := by
  rw [maxOn_eq_maxOn?_get]

@[simp, grind =]
theorem isSome_maxOn_iff_ne_nil
    [LE β] [DecidableLE β] {f : α → β} {xs : List α} :
    (xs.maxOn? f).isSome ↔ xs ≠ [] := by
  fun_cases xs.maxOn? f <;> simp

theorem maxOn_eq_of_maxOn?_eq_some
    [LE β] [DecidableLE β] {f : α → β} {xs : List α} {x : α} (h : xs.maxOn? f = some x) :
    xs.maxOn f (isSome_maxOn_iff_ne_nil.mp (Option.isSome_of_eq_some h)) = x := by
  have h' := isSome_maxOn_iff_ne_nil.mp (Option.isSome_of_eq_some h)
  rwa [maxOn?_eq_some_maxOn h', Option.some.injEq] at h

@[grind =>]
theorem isSome_maxOn?_of_mem
    [LE β] [DecidableLE β] {f : α → β} {xs : List α} {x : α} (h : x ∈ xs) :
    (xs.maxOn? f).isSome := by
  apply isSome_maxOn?_of_ne_nil
  exact ne_nil_of_mem h

theorem le_apply_maxOn?_get_of_mem
    [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {f : α → β} {xs : List α} {x : α} (h : x ∈ xs) :
    f x ≤ f ((xs.maxOn? f).get (isSome_maxOn?_of_mem h)) := by
  rw [maxOn?_get_eq_maxOn (ne_nil_of_mem h)]
  apply le_apply_maxOn_of_mem h

-- The suggested patterns are not useful because all involve `IsLinearPreorder`.
grind_pattern List.le_apply_maxOn?_get_of_mem => x ∈ xs, (xs.maxOn? f).get _

theorem maxOn?_left_leaning [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {xs : List α} {f : α → β} {x : α}
    (hx : xs.maxOn? f = some x) :
    ∃ j : Fin xs.length, xs[j] = x ∧ ∀ i : Fin j, ¬ f x ≤ f xs[i] := by
  rw [← maxOn_eq_of_maxOn?_eq_some hx]
  apply List.maxOn_left_leaning

@[grind <=]
theorem maxOn?_mem [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {xs : List α} {f : α → β}
    (h : xs.maxOn? f = some a) : a ∈ xs := by
  rw [← maxOn_eq_of_maxOn?_eq_some h]
  apply maxOn_mem

theorem maxOn?_replicate [LE β] [DecidableLE β] [Std.IsLinearPreorder β]
    {n : Nat} {a : α} {f : α → β} :
    (replicate n a).maxOn? f = if n = 0 then none else some a := by
  split
  · simp [*]
  · rw [maxOn?_eq_some_maxOn, maxOn_replicate]
    simp [*]

@[simp, grind =]
theorem maxOn?_replicate_of_pos [LE β] [DecidableLE β] [Std.IsLinearPreorder β]
    {n : Nat} {a : α} {f : α → β} (h : 0 < n) :
    (replicate n a).maxOn? f = some a := by
  simp [maxOn?_replicate, show n ≠ 0 from Nat.ne_zero_of_lt h]

@[grind =]
theorem List.maxOn?_append [LE β] [DecidableLE β] [Std.IsLinearPreorder β] (xs ys : List α) (f : α → β) :
    (xs ++ ys).maxOn? f =
      (xs.maxOn? f).merge (_root_.maxOn f) (ys.maxOn? f) := by
  by_cases xs = [] <;> by_cases ys = [] <;> simp [*, maxOn?_eq_if, maxOn_append]

end List
