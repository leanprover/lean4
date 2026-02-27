/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Markus Himmel
-/
module

prelude
public import Init.Data.String.Slice
public import Init.Data.String.Search
public import Init.Data.List.SplitOn.Basic
import Init.Data.String.Termination
import Init.Data.Order.Lemmas
import Init.Data.Iterators.Lemmas.Combinators.FilterMap
import Init.Data.String.Lemmas.Pattern.Split.Basic
import Init.Data.String.Lemmas.Pattern.Char
import Init.ByCases
import Init.Data.String.OrderInstances
import Init.Data.String.Lemmas.Order
import Init.Data.String.Lemmas.Intercalate
import Init.Data.List.SplitOn.Lemmas

public section

namespace String.Slice

open Pattern.Model Pattern.Model.Char

theorem toList_splitToSubslice_char {s : Slice} {c : Char} :
    (s.splitToSubslice c).toList.map (Slice.copy ∘ Subslice.toSlice) =
      (s.copy.toList.splitOn c).map String.ofList := by
  simp only [Pattern.toList_splitToSubslice_eq_modelSplit]
  suffices ∀ (f p : s.Pos) (hle : f ≤ p) (t₁ t₂ : String),
      p.Splits t₁ t₂ → (Pattern.Model.split c f p hle).map (copy ∘ Subslice.toSlice) =
        (t₂.toList.splitOnPPrepend (· == c) (s.subslice f p hle).copy.toList.reverse).map String.ofList by
    simpa [List.splitOn_eq_splitOnP] using this s.startPos s.startPos (Std.le_refl _) "" s.copy
  intro f p hle t₁ t₂ hp
  induction p using Pos.next_induction generalizing f t₁ t₂ with
  | next p h ih =>
    obtain ⟨t₂, rfl⟩ := hp.exists_eq_singleton_append h
    by_cases hpc : p.get h = c
    · simp [split_eq_of_isLongestMatchAt (isLongestMatchAt_of_get_eq hpc),
        ih _ (Std.le_refl _) _ _ hp.next,
        List.splitOnPPrepend_cons_pos (p := (· == c)) (beq_iff_eq.2 hpc)]
    · rw [split_eq_next_of_not_matchesAt h (not_matchesAt_of_get_ne hpc)]
      simp only [toList_append, toList_singleton, List.cons_append, List.nil_append, Subslice.copy_eq]
      rw [ih _ _ _ _ hp.next, List.splitOnPPrepend_cons_neg (by simpa)]
      have := (splits_slice (Std.le_trans hle (by simp)) (p.slice f (p.next h) hle (by simp))).eq_append
      simp_all
  | endPos => simp_all

theorem toList_split_char {s : Slice} {c : Char} :
    (s.split c).toList.map Slice.copy = (s.copy.toList.splitOn c).map String.ofList := by
  simp [toList_split_eq_splitToSubslice, ← toList_splitToSubslice_char]

end Slice

theorem toList_split_char {s : String} {c : Char} :
    (s.split c).toList.map Slice.copy = (s.toList.splitOn c).map String.ofList := by
  simp [split_eq_split_toSlice, Slice.toList_split_char]

theorem Slice.toList_split_intercalate {c : Char} {l : List Slice} (hl : ∀ s ∈ l, c ∉ s.copy.toList) :
    ((Slice.intercalate (String.singleton c) l).split c).toList.map Slice.copy =
      if l = [] then [""] else l.map Slice.copy := by
  simp [String.toList_split_char]
  split
  · simp_all
  · rw [List.splitOn_intercalate] <;> simp_all

theorem toList_split_intercalate {c : Char} {l : List String} (hl : ∀ s ∈ l, c ∉ s.toList) :
    ((String.intercalate (String.singleton c) l).split c).toList.map (·.copy) =
      if l = [] then [""] else l := by
  simp only [toList_split_char, toList_intercalate, toList_singleton]
  split
  · simp_all
  · rw [List.splitOn_intercalate] <;> simp_all

end String
