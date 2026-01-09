/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Order.MinMaxOn
public import Init.Data.Int.OfNat
import Init.Data.Order.Lemmas
import Init.Data.List.Lemmas
import Init.Data.List.Sublist
import Init.Data.List.MinMax

set_option doc.verso true
set_option linter.missingDocs true

namespace List

/--
Returns an element of the non-empty list {name}`l` that minimizes {name}`f`. If {given}`x, y` are
such that {lean}`f x = f y`, it returns whichever comes first in the list.
-/
@[inline, suggest_for List.argmin]
public protected def minOn [LE β] [DecidableLE β] (f : α → β) (l : List α) (h : l ≠ []) : α :=
  match l with
  | x :: xs => xs.foldl (init := x) (minOn f)

/--
Returns an element of the non-empty list {name}`l` that maximizes {name}`f`. If {given}`x, y` are
such that {lean}`f x = f y`, it returns whichever comes first in the list.
-/
@[inline, suggest_for List.argmax]
public protected def maxOn [LE β] [DecidableLE β] (f : α → β) (l : List α) (h : l ≠ []) : α :=
  match l with
  | x :: xs => xs.foldl (init := x) (maxOn f)

/--
Returns an element of {name}`l` that minimizes {name}`f`. If {given}`x, y` are such that
{lean}`f x = f y`, it returns whichever comes first in the list. Returns {name}`none` if the list is
empty.
-/
@[inline, suggest_for List.argmin? List.argmin] -- Mathlib's `List.argmin` returns an `Option α`
public protected def minOn? [LE β] [DecidableLE β] (f : α → β) (l : List α) : Option α :=
  match l with
  | [] => none
  | x :: xs => some (xs.foldl (init := x) (minOn f))

/--
Returns an element of {name}`l` that maximizes {name}`f`. If {given}`x, y` are such that
{lean}`f x = f y`, it returns whichever comes first in the list. Returns {name}`none` if the list is
empty.
-/
@[inline, suggest_for List.argmax? List.argmax] -- Mathlib's `List.argmax` returns an `Option α`
public protected def maxOn? [LE β] [DecidableLE β] (f : α → β) (l : List α) : Option α :=
  match l with
  | [] => none
  | x :: xs => some (xs.foldl (init := x) (maxOn f))

/-! ### maxOn -/

@[simp, grind =]
public theorem maxOn_singleton [LE β] [DecidableLE β] {x : α} {f : α → β} :
    [x].maxOn f (of_decide_eq_false rfl) = x := by
  simp [List.maxOn]

public theorem maxOn_cons
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
  rw [apply_maxOn_le_iff]
  intro x hx
  exact le_apply_maxOn_of_mem (hxs hx)

theorem apply_maxOn_take_le [LE β] [DecidableLE β] [Std.IsLinearPreorder β]
    {xs : List α} {f : α → β} {n : Nat} (h : xs.take n ≠ []) :
    f ((xs.take n).maxOn f h) ≤ f (xs.maxOn f (List.ne_nil_of_take_ne_nil h)) := by
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
