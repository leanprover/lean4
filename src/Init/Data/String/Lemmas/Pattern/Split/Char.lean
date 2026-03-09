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
public import Init.Data.String.Lemmas.Pattern.Split.Basic
public import Init.Data.String.Lemmas.Pattern.Char
import all Init.Data.String.Lemmas.Pattern.Split.Basic
import Init.Data.String.Termination
import Init.Data.Order.Lemmas
import Init.Data.Iterators.Lemmas.Combinators.FilterMap
import Init.Data.String.Lemmas.Pattern.Split.Basic
import Init.Data.String.Lemmas.Pattern.Split.Pred
import Init.Data.String.Lemmas.Pattern.Char
import Init.ByCases
import Init.Data.String.OrderInstances
import Init.Data.String.Lemmas.Order
import Init.Data.String.Lemmas.Intercalate
import Init.Data.List.SplitOn.Lemmas

public section

namespace String.Slice

open Pattern.Model Pattern.Model.Char

theorem Pattern.Model.split_char_eq_split_beq {c : Char} {s : Slice}
    (f curr : s.Pos) (hle : f ≤ curr) :
    Model.split c f curr hle = Model.split (· == c) f curr hle := by
  fun_induction Model.split c f curr hle with
  | case1 fr h => simp
  | case2 fr curr hle h pos h₁ h₂ ih =>
    conv => rhs; rw [Model.split]
    simp only [h, ↓reduceDIte]
    split <;> simp_all [matchAt?_eq_matchAt?_beq]
  | case3 fr curr hle h pos ih =>
    conv => rhs; rw [Model.split]
    simp only [h, ↓reduceDIte]
    split <;> simp_all [matchAt?_eq_matchAt?_beq]

theorem toList_splitToSubslice_char {s : Slice} {c : Char} :
    (s.splitToSubslice c).toList.map (Slice.copy ∘ Subslice.toSlice) =
      (s.copy.toList.splitOn c).map String.ofList := by
  have : (s.splitToSubslice c).toList = (s.splitToSubslice (· == c)).toList := by
    simp only [Pattern.toList_splitToSubslice_eq_modelSplit, Pattern.Model.split_char_eq_split_beq]
  simp only [this, List.splitOn_eq_splitOnP, toList_splitToSubslice_bool]

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
