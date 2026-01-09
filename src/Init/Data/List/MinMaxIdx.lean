/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
module

prelude
public import Init.Data.List.MinMaxOn
public import Init.Data.List.Pairwise
public import Init.Data.Subtype.Order
import Init.Data.Order.Lemmas
import Init.Data.List.Nat.TakeDrop

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

theorem minIdxOn_lt_length [LE β] [DecidableLE β] {f : α → β} {xs : List α} (h : xs ≠ []) :
    xs.minIdxOn f h < xs.length := by
  rw [minIdxOn.eq_def]
  split
  simp [minIdxOn.go_lt_length_add]

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

private theorem aux {xs : List α} {k : Nat} {y : α} {ys : List α} (h : xs.drop k = y :: ys) :
    xs.take (k + 1) = xs.take k ++ [y] := by
  have hlt : k < xs.length := by
    false_or_by_contra
    have : drop k xs = [] := drop_of_length_le (by omega)
    simp [this] at h
  rw [take_succ_eq_append_getElem hlt]
  have := take_append_drop k xs
  rw [h] at this
  conv => lhs; rhs; simp +singlePass only [← this]
  rw [getElem_append_right (length_take_le _ _)]
  simp [length_take_of_le (Nat.le_of_lt hlt)]

private theorem minIdxOn_eq_go_drop [LE β] [DecidableLE β] [IsLinearPreorder β] {f : α → β} {xs : List α} (h : xs ≠ [])
    {k : Nat} :
    ∃ i, i ≤ k ∧ xs.minIdxOn f h = List.minIdxOn.go f ((xs.take (k + 1)).minOn f (by cases xs <;> simp_all)) i (k + 1) (xs.drop (k + 1)) := by
  match xs with
  | y :: ys =>
    simp only [drop_succ_cons]
    induction k generalizing xs
    · simp [minIdxOn]
    · rename_i k ih
      specialize ih (xs := xs)
      obtain ⟨i, hi, ih⟩ := ih
      simp only [ih, ← drop_drop]
      match h : drop k ys with
      | [] =>
        simp [drop_nil, minIdxOn.go, show i ≤ k + 1 from Nat.le_succ_of_le ‹i ≤ k›]
      | z :: zs =>
        simp only [minIdxOn.go]
        split
        · have : take (k + 1 + 1) (y :: ys) = take (k + 1) (y :: ys) ++ [z] := by apply aux ‹_›
          simp only [this]
          conv => congr; ext; rhs; rw [List.minOn_append (by simp) (by simp)]
          simp_all [minOn_eq_left]
          exact ⟨i, Nat.le_succ_of_le ‹i ≤ k›, rfl⟩
        · have : take (k + 1 + 1) (y :: ys) = take (k + 1) (y :: ys) ++ [z] := by apply aux ‹_›
          simp only [this]
          conv => congr; ext; rhs; rw [List.minOn_append (by simp) (by simp)]
          simp_all [minOn_eq_right]
          exact ⟨k + 1, Nat.le_refl _, rfl⟩

theorem minIdxOn_le_of_getElem_le [LE β] [DecidableLE β] [IsLinearPreorder β]
    {f : α → β} {xs : List α} (h : xs ≠ [])
    {k : Nat} (hi : k < xs.length) (hle : f xs[k] ≤ f (xs.minOn f h)) :
    xs.minIdxOn f h ≤ k := by
  obtain ⟨i, hi, h'⟩ := minIdxOn_eq_go_drop (f := f) h (k := k)
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
  obtain ⟨i, hi, h'⟩ := minIdxOn_eq_go_drop (f := f) h (k := xs.length)
  rw [drop_eq_nil_of_le (by omega)] at h'
  simp only [take_of_length_le (l := xs) (i := xs.length + 1) (by omega)] at h'
  simp only [minIdxOn.go] at h'
  simp only [minIdxOn]
  split


theorem minIdxOn_eq_iff [LE β] [DecidableLE β] [IsLinearPreorder β]
    {f : α → β} {xs : List α} (h : xs ≠ []) {i : Nat} :
    xs.minIdxOn f h = i ↔ ∃ hr : i < xs.length, xs[i] = xs.minOn f h ∧
      ∀ (j : Nat) (hs : j < i), ¬ f xs[j] ≤ f xs[i] := by
  apply Iff.intro
  · rintro rfl
    refine ⟨List.minIdxOn_lt_length h, ?_⟩

end List
