/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Array.Sort.Basic
import all Init.Data.Array.Sort.Basic
import all Init.Data.List.Sort.Basic
public import Init

-- TODO:
import all Init.Data.Slice.Array.Lemmas
public import Init

section ToDo

theorem Subarray.sliceSize_eq_size {xs : Subarray α} :
    Std.Slice.size xs = xs.size := by
  rfl

theorem Subarray.getElem_eq_getElem_array {xs : Subarray α} {h : i < xs.size} :
    xs[i] = xs.array[xs.start + i]'(by simp only [size] at h; have := xs.stop_le_array_size; omega) := by
  rfl

-- The current `List.extract_eq_drop_take` should be called `List.extract_eq_take_drop`
@[simp] theorem List.extract_eq_drop_take' {l : List α} {start stop : Nat} :
    l.extract start stop = (l.take stop).drop start := by
  simp [List.take_drop]
  by_cases start ≤ stop
  · simp [*]
  · have h₁ : stop - start = 0 := by omega
    have h₂ : min stop l.length ≤ stop := by omega
    simp only [Nat.add_zero, drop_take_self, nil_eq, drop_eq_nil_iff, length_take, ge_iff_le, h₁]
    omega

theorem Subarray.toList_eq_drop_take {xs : Subarray α} :
    xs.toList = (xs.array.toList.take xs.stop).drop xs.start := by
  rw [Subarray.toList_eq, Array.toList_extract, List.extract_eq_drop_take']

theorem Subarray.getElem_toList {xs : Subarray α} {h : i < xs.toList.length} :
    xs.toList[i]'h = xs[i]'(by simpa using h) := by
  simp [getElem_eq_getElem_array, toList_eq_drop_take]

theorem Subarray.getElem_eq_getElem_toList {xs : Subarray α} {h : i < xs.size} :
    xs[i]'h = xs.toList[i]'(by simpa using h) := by
  rw [getElem_toList]

-- theorem Std.Slice.fold_iter [ToIterator (Slice γ) Id α β]
--     [Iterator α Id β] [IteratorLoop α Id Id] [Iterators.Finite α Id] {s : Slice γ} :
--     s.iter.fold (init := init) f = s.foldl (init := init) f := by
--   rfl

theorem Std.Slice.foldl_toList [ToIterator (Slice γ) Id α β]
    [Iterator α Id β] [IteratorLoop α Id Id] [LawfulIteratorLoop α Id Id]
    [Iterators.Finite α Id] {s : Slice γ} :
    s.toList.foldl (init := init) f = s.foldl (init := init) f := by
  sorry

theorem Subarray.foldl_toList {xs : Subarray α} :
    xs.toList.foldl (init := init) f = xs.foldl (init := init) f := by
  sorry

theorem Subarray.toList_drop {xs : Subarray α} :
    (xs.drop n).toList = xs.toList.drop n := by
  sorry

theorem Array.MergeSort.merge.go_eq_listMerge {xs ys : Subarray α} {hxs hys le acc} :
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
      simp [this]
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

attribute [- simp] List.mkSlice_rio_eq_mkSlice_rco
  Array.mkSlice_rci_eq_mkSlice_rco
  Subarray.mkSlice_rio_eq_mkSlice_rco Subarray.mkSlice_rci_eq_mkSlice_rco

theorem Array.MergeSort.merge_eq_listMerge {xs ys : Array α} {le} :
    (Array.MergeSort.Internal.merge xs ys le).toList = List.merge xs.toList ys.toList le := by
  rw [Array.MergeSort.Internal.merge]
  split <;> rename_i heq₁
  · split <;> rename_i heq₂
    · simp [Array.MergeSort.merge.go_eq_listMerge]
    · have : ys.toList = [] := by simp_all
      simp [this]
  · have : xs.toList = [] := by simp_all
    simp [this]

theorem List.mergeSort_eq_merge_mkSlice {xs : List α} :
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
    simp +zetaDelta [Array.MergeSort.merge_eq_listMerge, Subarray.sliceSize_eq_size, *]
  · simp [List.mergeSort_eq_merge_mkSlice, Subarray.sliceSize_eq_size, *]

theorem Array.toList_mergeSort {xs : Array α} {le : α → α → Bool} :
    (xs.mergeSort le).toList = xs.toList.mergeSort le := by
  rw [Array.mergeSort, Subarray.toList_mergeSort, Array.toList_mkSlice_rii]
