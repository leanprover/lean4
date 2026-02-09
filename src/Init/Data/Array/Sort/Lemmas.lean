/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
import Init.Data.Slice.Array.Lemmas
import Init.Data.Slice.List.Lemmas
import Init.Data.Array.Bootstrap
import Init.Data.Array.Lemmas
import Init.ByCases
public import Init.Data.Array.Sort.Basic
public import Init.Data.List.Sort.Basic
import all Init.Data.Array.Sort.Basic
import all Init.Data.List.Sort.Basic
import Init.Data.List.Sort.Lemmas

public section

private theorem Array.MergeSort.merge.go_eq_listMerge {xs ys : Subarray α} {hxs hys le acc} :
    (Array.MergeSort.Internal.merge.go le xs ys hxs hys acc).toList = acc.toList ++ List.merge xs.toList ys.toList le := by
  fun_induction Array.MergeSort.Internal.merge.go le xs ys hxs hys acc
  · rename_i xs ys _ _ _ _ _ _ _ _
    rw [List.merge.eq_def]
    split
    · have : xs.size = 0 := by simp [← Subarray.length_toList, *]
      omega
    · have : ys.size = 0 := by simp [← Subarray.length_toList, *]
      omega
    · rename_i x' xs' y' ys' _ _
      simp +zetaDelta only at *
      have h₁ : x' = xs[0] := by simp [Subarray.getElem_eq_getElem_toList, *]
      have h₂ : y' = ys[0] := by simp [Subarray.getElem_eq_getElem_toList, *]
      cases h₁
      cases h₂
      simp [Subarray.toList_drop, *]
  · rename_i xs ys _ _ _ _ _ _ _
    rw [List.merge.eq_def]
    split
    · have : xs.size = 0 := by simp [← Subarray.length_toList, *]
      omega
    · have : ys.size = 0 := by simp [← Subarray.length_toList, *]
      omega
    · rename_i x' xs' y' ys' _ _
      simp +zetaDelta only at *
      have h₁ : x' = xs[0] := by simp [Subarray.getElem_eq_getElem_toList, *]
      have h₂ : y' = ys[0] := by simp [Subarray.getElem_eq_getElem_toList, *]
      cases h₁
      cases h₂
      simp [*]
      have : xs.size = xs'.length + 1 := by simp [← Subarray.length_toList, *]
      have : xs' = [] := List.eq_nil_of_length_eq_zero (by omega)
      simp only [this]
      rw [← Subarray.foldl_toList]
      simp [*]
  · rename_i xs ys _ _ _ _ _ _ _ _
    rw [List.merge.eq_def]
    split
    · have : xs.size = 0 := by simp [← Subarray.length_toList, *]
      omega
    · have : ys.size = 0 := by simp [← Subarray.length_toList, *]
      omega
    · rename_i x' xs' y' ys' _ _
      simp +zetaDelta only at *
      have h₁ : x' = xs[0] := by simp [Subarray.getElem_eq_getElem_toList, *]
      have h₂ : y' = ys[0] := by simp [Subarray.getElem_eq_getElem_toList, *]
      cases h₁
      cases h₂
      simp [Subarray.toList_drop, *]
  · rename_i xs ys _ _ _ _ _ _ _
    rw [List.merge.eq_def]
    split
    · have : xs.size = 0 := by simp [← Subarray.length_toList, *]
      omega
    · have : ys.size = 0 := by simp [← Subarray.length_toList, *]
      omega
    · rename_i x' xs' y' ys' _ _
      simp +zetaDelta only at *
      have h₁ : x' = xs[0] := by simp [Subarray.getElem_eq_getElem_toList, *]
      have h₂ : y' = ys[0] := by simp [Subarray.getElem_eq_getElem_toList, *]
      cases h₁
      cases h₂
      simp [*]
      have : ys.size = ys'.length + 1 := by simp [← Subarray.length_toList, *]
      have : ys' = [] := List.eq_nil_of_length_eq_zero (by omega)
      simp [this]
      rw [← Subarray.foldl_toList]
      simp [*]

private theorem Array.MergeSort.merge_eq_listMerge {xs ys : Array α} {le} :
    (Array.MergeSort.Internal.merge xs ys le).toList = List.merge xs.toList ys.toList le := by
  rw [Array.MergeSort.Internal.merge]
  split <;> rename_i heq₁
  · split <;> rename_i heq₂
    · simp [Array.MergeSort.merge.go_eq_listMerge]
    · have : ys.toList = [] := by simp_all
      simp [this]
  · have : xs.toList = [] := by simp_all
    simp [this]

private theorem List.mergeSort_eq_merge_mkSlice {xs : List α} :
    xs.mergeSort le =
      if 1 < xs.length then
        merge (xs[*...((xs.length + 1) / 2)].toList.mergeSort le) (xs[((xs.length + 1) / 2)...*].toList.mergeSort le) le
      else
        xs := by
  fun_cases xs.mergeSort le
  · simp
  · simp
  · rename_i x y ys lr hl hr
    simp [lr]

theorem Subarray.toList_mergeSort {xs : Subarray α} {le : α → α → Bool} :
    (xs.mergeSort le).toList = xs.toList.mergeSort le := by
  fun_induction xs.mergeSort le
  · rw [List.mergeSort_eq_merge_mkSlice]
    simp +zetaDelta [Array.MergeSort.merge_eq_listMerge, *]
  · simp [List.mergeSort_eq_merge_mkSlice, *]

theorem Array.toList_mergeSort {xs : Array α} {le : α → α → Bool} :
    (xs.mergeSort le).toList = xs.toList.mergeSort le := by
  rw [Array.mergeSort, Subarray.toList_mergeSort, Array.toList_mkSlice_rii]
