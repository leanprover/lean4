/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
import all Init.Data.Slice.List.Basic
public import Init.Data.Slice.List.Iterator
import all Init.Data.Slice.List.Iterator
import all Init.Data.Slice.Operations
import all Init.Data.Range.Polymorphic.Iterators
import all Init.Data.Range.Polymorphic.Lemmas
public import Init.Data.Slice.Lemmas
public import Init.Data.Iterators.Lemmas

open Std Std.PRange Std.Slice

namespace ListSlice

theorem internalIter_eq {α : Type u} {s : ListSlice α} :
    Internal.iter s = match s.internalRepresentation.stop with
        | some stop => s.internalRepresentation.list.iter.take stop
        | none => s.internalRepresentation.list.iter.toTake := by
  simp only [Internal.iter, ToIterator.iter_eq]; rfl

theorem toList_internalIter {α : Type u} {s : ListSlice α} :
    (Internal.iter s).toList = match s.internalRepresentation.stop with
        | some stop => s.internalRepresentation.list.take stop
        | none => s.internalRepresentation.list := by
  simp only [internalIter_eq]
  split <;> simp

theorem internalIter_eq_toIteratorIter {α : Type u} {s : ListSlice α} :
    Internal.iter s = ToIterator.iter s :=
  rfl

public instance : LawfulSliceSize (Internal.ListSliceData α) where
  lawful s := by
    simp [← internalIter_eq_toIteratorIter, SliceSize.size]

public theorem toList_eq {xs : ListSlice α} :
    xs.toList = match xs.internalRepresentation.stop with
      | some stop => xs.internalRepresentation.list.take stop
      | none => xs.internalRepresentation.list := by
  simp only [Std.Slice.toList, toList_internalIter]
  rfl

@[simp, grind =]
public theorem toArray_toList {xs : ListSlice α} :
    xs.toList.toArray = xs.toArray := by
  simp [Std.Slice.toArray, Std.Slice.toList]

@[simp, grind =]
public theorem toList_toArray {xs : ListSlice α} :
    xs.toArray.toList = xs.toList := by
  simp [Std.Slice.toArray, Std.Slice.toList]

@[simp, grind =]
public theorem length_toList {xs : ListSlice α} :
    xs.toList.length = xs.size := by
  simp [ListSlice.toList_eq, Std.Slice.size, Std.Slice.SliceSize.size, ← Iter.length_toList_eq_count,
    toList_internalIter]; rfl

@[grind =]
public theorem size_eq_length_toList {xs : ListSlice α} :
    xs.size = xs.toList.length :=
  length_toList.symm

@[simp, grind =]
public theorem size_toArray {xs : ListSlice α} :
    xs.toArray.size = xs.size := by
  simp [← ListSlice.toArray_toList]

end ListSlice

namespace List

@[simp, grind =]
public theorem toList_mkSlice_rco {xs : List α} {lo hi : Nat} :
    xs[lo...hi].toList = (xs.take hi).drop lo := by
  rw [List.take_eq_take_min, List.drop_eq_drop_min]
  simp only [Std.Rco.Sliceable.mkSlice, toSlice, ListSlice.toList_eq]
  by_cases h : lo < hi
  · have : lo ≤ hi := by omega
    simp [h, List.take_drop, Nat.add_sub_cancel' ‹_›, ← List.take_eq_take_min]
  · have : min hi xs.length ≤ lo := by omega
    simp [h, Nat.min_eq_right this]

@[simp, grind =]
public theorem toArray_mkSlice_rco {xs : List α} {lo hi : Nat} :
    xs[lo...hi].toArray = ((xs.take hi).drop lo).toArray := by
  simp [← ListSlice.toArray_toList]

@[simp, grind =]
public theorem size_mkSlice_rco {xs : List α} {lo hi : Nat} :
    xs[lo...hi].size = min hi xs.length - lo := by
  simp [← ListSlice.length_toList]

@[simp, grind =]
public theorem mkSlice_rcc_eq_mkSlice_rco {xs : List α} {lo hi : Nat} :
    xs[lo...=hi] = xs[lo...(hi + 1)] := by
  simp [Std.Rcc.Sliceable.mkSlice, Std.Rco.Sliceable.mkSlice]

@[simp]
public theorem toList_mkSlice_rcc {xs : List α} {lo hi : Nat} :
    xs[lo...=hi].toList = (xs.take (hi + 1)).drop lo := by
  simp

@[simp]
public theorem toArray_mkSlice_rcc {xs : List α} {lo hi : Nat} :
    xs[lo...=hi].toArray = ((xs.take (hi + 1)).drop lo).toArray := by
  simp [← ListSlice.toArray_toList]

@[simp]
public theorem size_mkSlice_rcc {xs : List α} {lo hi : Nat} :
    xs[lo...=hi].size = min (hi + 1) xs.length - lo := by
  simp [← ListSlice.length_toList]

@[simp]
public theorem toList_mkSlice_rci {xs : List α} {lo : Nat} :
    xs[lo...*].toList = xs.drop lo := by
  rw [List.drop_eq_drop_min]
  simp [ListSlice.toList_eq, Std.Rci.Sliceable.mkSlice, List.toUnboundedSlice]

@[simp]
public theorem toArray_mkSlice_rci {xs : List α} {lo : Nat} :
    xs[lo...*].toArray = (xs.drop lo).toArray := by
  simp [← ListSlice.toArray_toList]

@[grind =]
public theorem toList_mkSlice_rci_eq_toList_mkSlice_rco {xs : List α} {lo : Nat} :
    xs[lo...*].toList = xs[lo...xs.length].toList := by
  simp

@[grind =]
public theorem toArray_mkSlice_rci_eq_toArray_mkSlice_rco {xs : List α} {lo : Nat} :
    xs[lo...*].toArray = xs[lo...xs.length].toArray := by
  simp

@[simp]
public theorem size_mkSlice_rci {xs : List α} {lo : Nat} :
    xs[lo...*].size = xs.length - lo := by
  simp [← ListSlice.length_toList]

@[simp, grind =]
public theorem mkSlice_roo_eq_mkSlice_rco {xs : List α} {lo hi : Nat} :
    xs[lo<...hi] = xs[(lo + 1)...hi] := by
  simp [Std.Roo.Sliceable.mkSlice, Std.Rco.Sliceable.mkSlice]

@[simp]
public theorem toList_mkSlice_roo {xs : List α} {lo hi : Nat} :
    xs[lo<...hi].toList = (xs.take hi).drop (lo + 1) := by
  simp

@[simp]
public theorem toArray_mkSlice_roo {xs : List α} {lo hi : Nat} :
    xs[lo<...hi].toArray = ((xs.take hi).drop (lo + 1)).toArray := by
  simp [← ListSlice.toArray_toList]

@[simp]
public theorem size_mkSlice_roo {xs : List α} {lo hi : Nat} :
    xs[lo<...hi].size = min hi xs.length - (lo + 1) := by
  simp [← ListSlice.length_toList]

@[simp]
public theorem mkSlice_roc_eq_mkSlice_roo {xs : List α} {lo hi : Nat} :
    xs[lo<...=hi] = xs[lo<...(hi + 1)] := by
  simp [Std.Roc.Sliceable.mkSlice, Std.Roo.Sliceable.mkSlice]

@[simp, grind =]
public theorem mkSlice_roc_eq_mkSlice_rco {xs : List α} {lo hi : Nat} :
    xs[lo<...=hi] = xs[(lo + 1)...(hi + 1)] := by
  simp

@[simp]
public theorem toList_mkSlice_roc {xs : List α} {lo hi : Nat} :
    xs[lo<...=hi].toList = (xs.take (hi + 1)).drop (lo + 1) := by
  simp

@[simp]
public theorem toArray_mkSlice_roc {xs : List α} {lo hi : Nat} :
    xs[lo<...=hi].toArray = ((xs.take (hi + 1)).drop (lo + 1)).toArray := by
  simp [← ListSlice.toArray_toList]

@[simp]
public theorem size_mkSlice_roc {xs : List α} {lo hi : Nat} :
    xs[lo<...=hi].size = min (hi + 1) xs.length - (lo + 1) := by
  simp [← ListSlice.length_toList]

@[simp, grind =]
public theorem mkSlice_roi_eq_mkSlice_rci {xs : List α} {lo : Nat} :
    xs[lo<...*] = xs[(lo + 1)...*] := by
  simp [Std.Roi.Sliceable.mkSlice, Std.Rci.Sliceable.mkSlice]

public theorem toList_mkSlice_roi_eq_toList_mkSlice_roo {xs : List α} {lo : Nat} :
    xs[lo<...*].toList = xs[lo<...xs.length].toList := by
  simp

public theorem toArray_mkSlice_roi_eq_toArray_mkSlice_roo {xs : List α} {lo : Nat} :
    xs[lo<...*].toArray = xs[lo<...xs.length].toArray := by
  simp

public theorem toList_mkSlice_roi_eq_toList_mkSlice_rco {xs : List α} {lo : Nat} :
    xs[lo<...*].toList = xs[(lo + 1)...xs.length].toList := by
  simp

public theorem toArray_mkSlice_roi_eq_toArray_mkSlice_rco {xs : List α} {lo : Nat} :
    xs[lo<...*].toArray = xs[(lo + 1)...xs.length].toArray := by
  simp

@[simp]
public theorem toList_mkSlice_roi {xs : List α} {lo : Nat} :
    xs[lo<...*].toList = xs.drop (lo + 1) := by
  simp

@[simp]
public theorem toArray_mkSlice_roi {xs : List α} {lo : Nat} :
    xs[lo<...*].toArray = (xs.drop (lo + 1)).toArray := by
  simp [← ListSlice.toArray_toList]

@[simp]
public theorem size_mkSlice_roi {xs : List α} {lo : Nat} :
    xs[lo<...*].size = xs.length - (lo + 1) := by
  simp [← ListSlice.length_toList]

@[simp, grind =]
public theorem mkSlice_rio_eq_mkSlice_rco {xs : List α} {hi : Nat} :
    xs[*...hi] = xs[0...hi] := by
  simp [Std.Rio.Sliceable.mkSlice, Std.Rco.Sliceable.mkSlice]

@[simp]
public theorem toList_mkSlice_rio {xs : List α} {hi : Nat} :
    xs[*...hi].toList = xs.take hi := by
  simp

@[simp]
public theorem toArray_mkSlice_rio {xs : List α} {hi : Nat} :
    xs[*...hi].toArray = (xs.take hi).toArray := by
  simp [← ListSlice.toArray_toList]

@[simp]
public theorem size_mkSlice_rio {xs : List α} {hi : Nat} :
    xs[*...hi].size = min hi xs.length := by
  simp [← ListSlice.length_toList]

@[simp]
public theorem mkSlice_ric_eq_mkSlice_rio {xs : List α} {hi : Nat} :
    xs[*...=hi] = xs[*...(hi + 1)] := by
  simp [Std.Ric.Sliceable.mkSlice, Std.Rio.Sliceable.mkSlice]

@[grind =]
public theorem mkSlice_ric_eq_mkSlice_rco {xs : List α} {hi : Nat} :
    xs[*...=hi] = xs[0...(hi + 1)] := by
  simp

@[simp]
public theorem toList_mkSlice_ric {xs : List α} {hi : Nat} :
    xs[*...=hi].toList = xs.take (hi + 1) := by
  simp

@[simp]
public theorem toArray_mkSlice_ric {xs : List α} {hi : Nat} :
    xs[*...=hi].toArray = (xs.take (hi + 1)).toArray := by
  simp [← ListSlice.toArray_toList]

@[simp]
public theorem size_mkSlice_ric {xs : List α} {hi : Nat} :
    xs[*...=hi].size = min (hi + 1) xs.length := by
  simp [← ListSlice.length_toList]

@[simp, grind =]
public theorem mkSlice_rii_eq_mkSlice_rci {xs : List α} :
    xs[*...*] = xs[0...*] := by
  simp [Std.Rii.Sliceable.mkSlice, Std.Rci.Sliceable.mkSlice]

public theorem toList_mkSlice_rii_eq_toList_mkSlice_rco {xs : List α} :
    xs[*...*].toList = xs[0...xs.length].toList := by
  simp

public theorem toArray_mkSlice_rii_eq_toArray_mkSlice_rco {xs : List α} :
    xs[*...*].toArray = xs[0...xs.length].toArray := by
  simp

@[simp]
public theorem toList_mkSlice_rii {xs : List α} :
    xs[*...*].toList = xs := by
  simp

@[simp]
public theorem toArray_mkSlice_rii {xs : List α} :
    xs[*...*].toArray = xs.toArray := by
  simp [← ListSlice.toArray_toList]

@[simp]
public theorem size_mkSlice_rii {xs : List α} :
    xs[*...*].size = xs.length := by
  simp [← ListSlice.length_toList]

end List

section ListSubslices

namespace ListSlice

@[simp, grind =]
public theorem toList_mkSlice_rco {xs : ListSlice α} {lo hi : Nat} :
    xs[lo...hi].toList = (xs.toList.take hi).drop lo := by
  simp only [instSliceableListSliceNat_1, List.toList_mkSlice_rco, ListSlice.toList_eq (xs := xs)]
  obtain ⟨⟨xs, stop⟩⟩ := xs
  cases stop
  · simp
  · simp [List.take_take, Nat.min_comm]

@[simp, grind =]
public theorem toArray_mkSlice_rco {xs : ListSlice α} {lo hi : Nat} :
    xs[lo...hi].toArray = xs.toArray.extract lo hi := by
  simp [← toArray_toList, List.drop_take]

@[simp, grind =]
public theorem mkSlice_rcc_eq_mkSlice_rco {xs : ListSlice α} {lo hi : Nat} :
    xs[lo...=hi] = xs[lo...(hi + 1)] := by
  simp [Std.Rcc.Sliceable.mkSlice, Std.Rco.Sliceable.mkSlice]

@[simp]
public theorem toList_mkSlice_rcc {xs : ListSlice α} {lo hi : Nat} :
    xs[lo...=hi].toList = (xs.toList.take (hi + 1)).drop lo := by
  simp

@[simp]
public theorem toArray_mkSlice_rcc {xs : ListSlice α} {lo hi : Nat} :
    xs[lo...=hi].toArray = xs.toArray.extract lo (hi + 1) := by
  simp [← ListSlice.toArray_toList, List.drop_take]

@[simp]
public theorem toList_mkSlice_rci {xs : ListSlice α} {lo : Nat} :
    xs[lo...*].toList = xs.toList.drop lo := by
  simp only [instSliceableListSliceNat_2, ListSlice.toList_eq (xs := xs)]
  obtain ⟨⟨xs, stop⟩⟩ := xs
  simp only
  split <;> simp

@[simp]
public theorem toArray_mkSlice_rci {xs : ListSlice α} {lo : Nat} :
    xs[lo...*].toArray = xs.toArray.extract lo := by
  simp only [← toArray_toList, toList_mkSlice_rci]
  rw (occs := [1]) [← List.take_length (l := List.drop lo xs.toList)]
  simp [- toArray_toList]

@[grind =]
public theorem toList_mkSlice_rci_eq_toList_mkSlice_rco {xs : ListSlice α} {lo : Nat} :
    xs[lo...*].toList = xs[lo...xs.size].toList := by
  simp [← length_toList, - Slice.length_toList_eq_size]

@[grind =]
public theorem toArray_mkSlice_rci_eq_toArray_mkSlice_rco {xs : ListSlice α} {lo : Nat} :
    xs[lo...*].toArray = xs[lo...xs.size].toArray := by
  simp

@[simp, grind =]
public theorem mkSlice_roo_eq_mkSlice_rco {xs : ListSlice α} {lo hi : Nat} :
    xs[lo<...hi] = xs[(lo + 1)...hi] := by
  simp [Std.Roo.Sliceable.mkSlice, Std.Rco.Sliceable.mkSlice]

@[simp]
public theorem toList_mkSlice_roo {xs : ListSlice α} {lo hi : Nat} :
    xs[lo<...hi].toList = (xs.toList.take hi).drop (lo + 1) := by
  simp

@[simp]
public theorem toArray_mkSlice_roo {xs : ListSlice α} {lo hi : Nat} :
    xs[lo<...hi].toArray = xs.toArray.extract (lo + 1) hi := by
  simp [← toArray_toList, List.drop_take]

@[simp]
public theorem mkSlice_roc_eq_mkSlice_roo {xs : ListSlice α} {lo hi : Nat} :
    xs[lo<...=hi] = xs[lo<...(hi + 1)] := by
  simp [Std.Roc.Sliceable.mkSlice, Std.Roo.Sliceable.mkSlice]

@[simp]
public theorem mkSlice_roc_eq_mkSlice_rcc {xs : ListSlice α} {lo hi : Nat} :
    xs[lo<...=hi] = xs[(lo + 1)...=hi] := by
  simp [Std.Roc.Sliceable.mkSlice, Std.Rco.Sliceable.mkSlice]

@[simp, grind =]
public theorem mkSlice_roc_eq_mkSlice_rco {xs : ListSlice α} {lo hi : Nat} :
    xs[lo<...=hi] = xs[(lo + 1)...(hi + 1)] := by
  simp [Std.Roc.Sliceable.mkSlice, Std.Rco.Sliceable.mkSlice]

@[simp]
public theorem toList_mkSlice_roc {xs : ListSlice α} {lo hi : Nat} :
    xs[lo<...=hi].toList = (xs.toList.take (hi + 1)).drop (lo + 1) := by
  simp

@[simp]
public theorem toArray_mkSlice_roc {xs : ListSlice α} {lo hi : Nat} :
    xs[lo<...=hi].toArray = xs.toArray.extract (lo + 1) (hi + 1) := by
  simp [← toArray_toList, List.drop_take]

@[simp, grind =]
public theorem mkSlice_roi_eq_mkSlice_rci {xs : ListSlice α} {lo : Nat} :
    xs[lo<...*] = xs[(lo + 1)...*] := by
  simp [Std.Roi.Sliceable.mkSlice, Std.Rci.Sliceable.mkSlice]

public theorem toList_mkSlice_roi_eq_toList_mkSlice_roo {xs : ListSlice α} {lo : Nat} :
    xs[lo<...*].toList = xs[lo<...xs.size].toList := by
  simp [← length_toList, - Slice.length_toList_eq_size]

public theorem toArray_mkSlice_roi_eq_toArray_mkSlice_roo {xs : ListSlice α} {lo : Nat} :
    xs[lo<...*].toArray = xs[lo<...xs.size].toArray := by
  simp only [mkSlice_roi_eq_mkSlice_rci, toArray_mkSlice_rci, size_toArray_eq_size,
    mkSlice_roo_eq_mkSlice_rco, toArray_mkSlice_rco]

public theorem toList_mkSlice_roi_eq_toList_mkSlice_rco {xs : ListSlice α} {lo : Nat} :
    xs[lo<...*].toList = xs[(lo + 1)...xs.size].toList := by
  simp [← length_toList, - Slice.length_toList_eq_size]

public theorem toArray_mkSlice_roi_eq_toArray_mkSlice_rco {xs : ListSlice α} {lo : Nat} :
    xs[lo<...*].toArray = xs[(lo + 1)...xs.size].toArray := by
  simp

@[simp]
public theorem toList_mkSlice_roi {xs : ListSlice α} {lo : Nat} :
    xs[lo<...*].toList = xs.toList.drop (lo + 1) := by
  simp

@[simp]
public theorem toArray_mkSlice_roi {xs : ListSlice α} {lo : Nat} :
    xs[lo<...*].toArray = xs.toArray.extract (lo + 1) := by
  simp only [← toArray_toList, toList_mkSlice_roi]
  rw (occs := [1]) [← List.take_length (l := List.drop (lo + 1) xs.toList)]
  simp [- toArray_toList]

@[simp, grind =]
public theorem mkSlice_rio_eq_mkSlice_rco {xs : ListSlice α} {hi : Nat} :
    xs[*...hi] = xs[0...hi] := by
  simp [Std.Rio.Sliceable.mkSlice, Std.Rco.Sliceable.mkSlice]

@[simp]
public theorem toList_mkSlice_rio {xs : ListSlice α} {hi : Nat} :
    xs[*...hi].toList = xs.toList.take hi := by
  simp

@[simp]
public theorem toArray_mkSlice_rio {xs : ListSlice α} {hi : Nat} :
    xs[*...hi].toArray = xs.toArray.extract 0 hi := by
  simp [← toArray_toList]

@[simp]
public theorem mkSlice_ric_eq_mkSlice_rio {xs : ListSlice α} {hi : Nat} :
    xs[*...=hi] = xs[*...(hi + 1)] := by
  simp [Std.Ric.Sliceable.mkSlice, Std.Rio.Sliceable.mkSlice]

@[simp]
public theorem mkSlice_ric_eq_mkSlice_rcc {xs : ListSlice α} {hi : Nat} :
    xs[*...=hi] = xs[0...=hi] := by
  simp [Std.Ric.Sliceable.mkSlice, Std.Rco.Sliceable.mkSlice]

@[grind =]
public theorem mkSlice_ric_eq_mkSlice_rco {xs : ListSlice α} {hi : Nat} :
    xs[*...=hi] = xs[0...(hi + 1)] := by
  simp [Std.Ric.Sliceable.mkSlice, Std.Rco.Sliceable.mkSlice]

@[simp]
public theorem toList_mkSlice_ric {xs : ListSlice α} {hi : Nat} :
    xs[*...=hi].toList = xs.toList.take (hi + 1) := by
  simp

@[simp]
public theorem toArray_mkSlice_ric {xs : ListSlice α} {hi : Nat} :
    xs[*...=hi].toArray = xs.toArray.extract 0 (hi + 1) := by
  simp [← toArray_toList]

@[simp, grind =]
public theorem mkSlice_rii {xs : ListSlice α} :
    xs[*...*] = xs := by
  simp [Std.Rii.Sliceable.mkSlice]

end ListSlice

end ListSubslices
