/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Array.Sort.Basic
public import Init.Data.List.Sort.Basic
public import Init.Data.Array.Perm
import all Init.Data.Array.Sort.Basic
import all Init.Data.List.Sort.Basic
import Init.Data.List.Sort.Lemmas
import Init.Data.Slice.Array.Lemmas
import Init.Data.Slice.List.Lemmas
import Init.Data.Array.Bootstrap
import Init.Data.Array.Lemmas
import Init.Data.Array.MapIdx
import Init.ByCases

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

@[simp, grind =]
theorem Subarray.mergeSort_eq_mergeSort_toArray {xs : Subarray α} {le : α → α → Bool} :
    xs.mergeSort le = xs.toArray.mergeSort le := by
  simp [← Array.toList_inj, toList_mergeSort, Array.mergeSort]

theorem Subarray.mergeSort_toArray {xs : Subarray α} {le : α → α → Bool} :
    xs.toArray.mergeSort le = xs.mergeSort le := by
  simp

theorem Array.toList_mergeSort {xs : Array α} {le : α → α → Bool} :
    (xs.mergeSort le).toList = xs.toList.mergeSort le := by
  rw [Array.mergeSort, Subarray.toList_mergeSort, Array.toList_mkSlice_rii]

theorem Array.mergeSort_eq_toArray_mergeSort_toList {xs : Array α} {le : α → α → Bool} :
    xs.mergeSort le = (xs.toList.mergeSort le).toArray := by
  simp [← toList_mergeSort]

/-!
# Basic properties of `Array.mergeSort`.

* `pairwise_mergeSort`: `mergeSort` produces a sorted array.
* `mergeSort_perm`: `mergeSort` is a permutation of the input array.
* `mergeSort_of_pairwise`: `mergeSort` does not change a sorted array.
* `sublist_mergeSort`: if `c` is a sorted sublist of `l`, then `c` is still a sublist of `mergeSort le l`.
-/

namespace Array

-- Enable this instance locally so we can write `Pairwise le` instead of `Pairwise (le · ·)` everywhere.
attribute [local instance] boolRelToRel

@[simp] theorem mergeSort_empty : (#[] : Array α).mergeSort r = #[] := by
  simp [mergeSort_eq_toArray_mergeSort_toList]

@[simp] theorem mergeSort_singleton {a : α} : #[a].mergeSort r = #[a] := by
  simp [mergeSort_eq_toArray_mergeSort_toList]

theorem mergeSort_perm {xs : Array α} {le} : (xs.mergeSort le).Perm xs := by
  simpa [mergeSort_eq_toArray_mergeSort_toList, Array.perm_iff_toList_perm] using List.mergeSort_perm _ _

@[simp] theorem size_mergeSort {xs : Array α} : (mergeSort xs le).size = xs.size := by
  simp [mergeSort_eq_toArray_mergeSort_toList]

@[simp] theorem mem_mergeSort {a : α} {xs : Array α} : a ∈ mergeSort xs le ↔ a ∈ xs := by
  simp [mergeSort_eq_toArray_mergeSort_toList]

/--
The result of `Array.mergeSort` is sorted,
as long as the comparison function is transitive (`le a b → le b c → le a c`)
and total in the sense that `le a b || le b a`.

The comparison function need not be irreflexive, i.e. `le a b` and `le b a` is allowed even when `a ≠ b`.
-/
theorem pairwise_mergeSort
    (trans : ∀ (a b c : α), le a b → le b c → le a c)
    (total : ∀ (a b : α), le a b || le b a)
    {xs : Array α} :
    (mergeSort xs le).toList.Pairwise (le · ·) := by
  simpa [mergeSort_eq_toArray_mergeSort_toList] using List.pairwise_mergeSort trans total _

/--
If the input array is already sorted, then `mergeSort` does not change the array.
-/
theorem mergeSort_of_pairwise {le : α → α → Bool} {xs : Array α} (_ : xs.toList.Pairwise (le · ·)) :
    mergeSort xs le = xs := by
  simpa [mergeSort_eq_toArray_mergeSort_toList, List.toArray_eq_iff] using List.mergeSort_of_pairwise ‹_›

/--
This merge sort algorithm is stable,
in the sense that breaking ties in the ordering function using the position in the array
has no effect on the output.

That is, elements which are equal with respect to the ordering function will remain
in the same order in the output array as they were in the input array.

See also:
* `sublist_mergeSort`: if `c <+ l` and `c.Pairwise le`, then `c <+ (mergeSort le l).toList`.
* `pair_sublist_mergeSort`: if `[a, b] <+ l` and `le a b`, then `[a, b] <+ (mergeSort le l).toList`)
-/
theorem mergeSort_zipIdx {xs : Array α} :
    (mergeSort (xs.zipIdx.map fun (a, i) => (a, i)) (List.zipIdxLE le)).map (·.1) = mergeSort xs le := by
  simpa [mergeSort_eq_toArray_mergeSort_toList, Array.toList_zipIdx] using List.mergeSort_zipIdx

/--
Another statement of stability of merge sort.
If `c` is a sorted sublist of `xs.toList`,
then `c` is still a sublist of `(mergeSort le xs).toList`.
-/
theorem sublist_mergeSort {le : α → α → Bool}
    (trans : ∀ (a b c : α), le a b → le b c → le a c)
    (total : ∀ (a b : α), le a b || le b a)
    {ys : List α} (_ : ys.Pairwise (le · ·)) (_ : List.Sublist ys xs.toList) :
    List.Sublist ys (mergeSort xs le).toList := by
  simpa [mergeSort_eq_toArray_mergeSort_toList, Array.toList_zipIdx] using
    List.sublist_mergeSort trans total ‹_› ‹_›

/--
Another statement of stability of merge sort.
If a pair `[a, b]` is a sublist of `xs.toList` and `le a b`,
then `[a, b]` is still a sublist of `(mergeSort le xs).toList`.
-/
theorem pair_sublist_mergeSort
    (trans : ∀ (a b c : α), le a b → le b c → le a c)
    (total : ∀ (a b : α), le a b || le b a)
    (hab : le a b) (h : List.Sublist [a, b] xs.toList) :
    List.Sublist [a, b] (mergeSort xs le).toList := by
  simpa [mergeSort_eq_toArray_mergeSort_toList, Array.toList_zipIdx] using
    List.pair_sublist_mergeSort trans total ‹_› ‹_›

theorem map_mergeSort {r : α → α → Bool} {s : β → β → Bool} {f : α → β}
    {xs : Array α} (hxs : ∀ a ∈ xs, ∀ b ∈ xs, r a b = s (f a) (f b)) :
    (xs.mergeSort r).map f = (xs.map f).mergeSort s := by
  simp only [mergeSort_eq_toArray_mergeSort_toList, List.map_toArray, toList_map, mk.injEq]
  apply List.map_mergeSort
  simpa

end Array
