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

open Std.Iterators Std.PRange

namespace Std.Slice.List

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

end Std.Slice.List

public theorem ListSlice.toList_eq {xs : ListSlice α} :
    xs.toList = match xs.internalRepresentation.stop with
      | some stop => xs.internalRepresentation.list.take stop
      | none => xs.internalRepresentation.list := by
  simp only [toList, List.ofSlice, Std.Slice.toList, ToIterator.state_eq]
  rw [Std.Slice.List.toList_internalIter]
  rfl

public theorem ListSlice.toArray_toList {xs : ListSlice α} :
    xs.toList.toArray = xs.toArray := by
  simp [ListSlice.toList, Std.Slice.toArray, List.ofSlice, Std.Slice.toList]

public theorem ListSlice.toList_toArray {xs : ListSlice α} :
    xs.toArray.toList = xs.toList := by
  simp [ListSlice.toList, Std.Slice.toArray, List.ofSlice, Std.Slice.toList]

@[simp]
public theorem ListSlice.length_toList {xs : ListSlice α} :
    xs.toList.length = xs.size := by
  simp [ListSlice.toList_eq, Std.Slice.size, Std.Slice.SliceSize.size, ← Iter.length_toList_eq_count]
  rw [Std.Slice.List.toList_internalIter]
  rfl

@[simp]
public theorem ListSlice.size_toArray {xs : ListSlice α} :
    xs.toArray.size = xs.size := by
  simp [← ListSlice.toArray_toList]

namespace List

@[simp]
public theorem toList_mkSlice_rco {xs : List α} {lo hi : Nat} :
    xs[lo...hi].toList = (xs.take hi).drop lo := by
  rw [List.take_eq_take_min, List.drop_eq_drop_min]
  simp [ListSlice.toList_eq, Std.Rco.Sliceable.mkSlice, List.toSlice]
  by_cases h : lo < hi
  · have : lo ≤ hi := by omega
    simp [h, List.take_drop, Nat.add_sub_cancel' ‹_›, ← List.take_eq_take_min]
  · have : min hi xs.length ≤ lo := by omega
    simp [h, Nat.min_eq_right this]

@[simp]
public theorem toArray_mkSlice_rco {xs : List α} {lo hi : Nat} :
    xs[lo...hi].toArray = ((xs.take hi).drop lo).toArray := by
  simp [← ListSlice.toArray_toList]

-- TODO: Keep these non-normal-form lemmas?
public theorem toArray_mkSlice_rco' {xs : List α} {lo hi : Nat} :
    xs[lo...hi].toArray = xs.toArray.extract lo hi := by
  simp [List.drop_take]

@[simp]
public theorem size_mkSlice_rco {xs : List α} {lo hi : Nat} :
    xs[lo...hi].size = min hi xs.length - lo := by
  simp [← ListSlice.length_toList]

@[simp]
public theorem mkSlice_rcc_eq_mkSlice_rco {xs : List α} {lo hi : Nat} :
    xs[lo...=hi] = xs[lo...(hi + 1)] := by
  simp [Std.Rcc.Sliceable.mkSlice, Std.Rco.Sliceable.mkSlice]

@[simp]
public theorem toList_mkSlice_rcc {xs : List α} {lo hi : Nat} :
    xs[lo...=hi].toList = (xs.take (hi + 1)).drop lo := by
  rw [mkSlice_rcc_eq_mkSlice_rco, toList_mkSlice_rco]

@[simp]
public theorem toArray_mkSlice_rcc {xs : List α} {lo hi : Nat} :
    xs[lo...=hi].toArray = ((xs.take (hi + 1)).drop lo).toArray := by
  simp [← ListSlice.toArray_toList]

public theorem toArray_mkSlice_rcc' {xs : List α} {lo hi : Nat} :
    xs[lo...=hi].toArray = xs.toArray.extract lo (hi + 1) := by
  simp [List.drop_take]

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

public theorem toArray_mkSlice_rci' {xs : List α} {lo : Nat} :
    xs[lo...*].toArray = xs.toArray.extract lo := by
  rw [toArray_mkSlice_rci]
  -- non-confluence between `take_length` and `drop_take`
  rw (occs := [1]) [← List.take_length (l := drop lo xs)]
  simp

@[simp]
public theorem size_mkSlice_rci {xs : List α} {lo : Nat} :
    xs[lo...*].size = xs.length - lo := by
  simp [← ListSlice.length_toList]

@[simp]
public theorem mkSlice_roo_eq_mkSlice_rco {xs : List α} {lo hi : Nat} :
    xs[lo<...hi] = xs[(lo + 1)...hi] := by
  simp [Std.Roo.Sliceable.mkSlice, Std.Rco.Sliceable.mkSlice]

@[simp]
public theorem toList_mkSlice_roo {xs : List α} {lo hi : Nat} :
    xs[lo<...hi].toList = (xs.take hi).drop (lo + 1) := by
  rw [mkSlice_roo_eq_mkSlice_rco, toList_mkSlice_rco]

@[simp]
public theorem toArray_mkSlice_roo {xs : List α} {lo hi : Nat} :
    xs[lo<...hi].toArray = ((xs.take hi).drop (lo + 1)).toArray := by
  simp [← ListSlice.toArray_toList]

public theorem toArray_mkSlice_roo' {xs : List α} {lo hi : Nat} :
    xs[lo<...hi].toArray = xs.toArray.extract (lo + 1) hi := by
  simp [List.drop_take]

@[simp]
public theorem size_mkSlice_roo {xs : List α} {lo hi : Nat} :
    xs[lo<...hi].size = min hi xs.length - (lo + 1) := by
  simp [← ListSlice.length_toList]

@[simp]
public theorem mkSlice_roc_eq_mkSlice_roo {xs : List α} {lo hi : Nat} :
    xs[lo<...=hi] = xs[lo<...(hi + 1)] := by
  simp [Std.Roc.Sliceable.mkSlice, Std.Roo.Sliceable.mkSlice]

@[simp]
public theorem toList_mkSlice_roc {xs : List α} {lo hi : Nat} :
    xs[lo<...=hi].toList = (xs.take (hi + 1)).drop (lo + 1) := by
  rw [mkSlice_roc_eq_mkSlice_roo, toList_mkSlice_roo]

@[simp]
public theorem toArray_mkSlice_roc {xs : List α} {lo hi : Nat} :
    xs[lo<...=hi].toArray = ((xs.take (hi + 1)).drop (lo + 1)).toArray := by
  simp [← ListSlice.toArray_toList]

public theorem toArray_mkSlice_roc' {xs : List α} {lo hi : Nat} :
    xs[lo<...=hi].toArray = xs.toArray.extract (lo + 1) (hi + 1) := by
  simp [List.drop_take]

@[simp]
public theorem size_mkSlice_roc {xs : List α} {lo hi : Nat} :
    xs[lo<...=hi].size = min (hi + 1) xs.length - (lo + 1) := by
  simp [← ListSlice.length_toList]

@[simp]
public theorem mkSlice_roi_eq_mkSlice_rci {xs : List α} {lo : Nat} :
    xs[lo<...*] = xs[(lo + 1)...*] := by
  simp [Std.Roi.Sliceable.mkSlice, Std.Rci.Sliceable.mkSlice]

@[simp]
public theorem toList_mkSlice_roi {xs : List α} {lo : Nat} :
    xs[lo<...*].toList = xs.drop (lo + 1) := by
  rw [mkSlice_roi_eq_mkSlice_rci, toList_mkSlice_rci]

@[simp]
public theorem toArray_mkSlice_roi {xs : List α} {lo : Nat} :
    xs[lo<...*].toArray = (xs.drop (lo + 1)).toArray := by
  simp [← ListSlice.toArray_toList]

public theorem toArray_mkSlice_roi' {xs : List α} {lo : Nat} :
    xs[lo<...*].toArray = xs.toArray.extract (lo + 1) := by
  rw [toArray_mkSlice_roi]
  rw (occs := [1]) [← List.take_length (l := drop (lo + 1) xs)]
  simp

@[simp]
public theorem size_mkSlice_roi {xs : List α} {lo : Nat} :
    xs[lo<...*].size = xs.length - (lo + 1) := by
  simp [← ListSlice.length_toList]

@[simp]
public theorem mkSlice_rio_eq_mkSlice_rco {xs : List α} {hi : Nat} :
    xs[*...hi] = xs[0...hi] := by
  simp [Std.Rio.Sliceable.mkSlice,
    Std.Rco.Sliceable.mkSlice]

@[simp]
public theorem toList_mkSlice_rio {xs : List α} {hi : Nat} :
    xs[*...hi].toList = xs.take hi := by
  rw [mkSlice_rio_eq_mkSlice_rco, toList_mkSlice_rco, List.drop_zero]

@[simp]
public theorem toArray_mkSlice_rio {xs : List α} {hi : Nat} :
    xs[*...hi].toArray = (xs.take hi).toArray := by
  simp [← ListSlice.toArray_toList]

public theorem toArray_mkSlice_rio' {xs : List α} {hi : Nat} :
    xs[*...hi].toArray = xs.toArray.extract 0 hi := by
  simp

@[simp]
public theorem size_mkSlice_rio {xs : List α} {hi : Nat} :
    xs[*...hi].size = min hi xs.length := by
  simp [← ListSlice.length_toList]

@[simp]
public theorem mkSlice_ric_eq_mkSlice_rio {xs : List α} {hi : Nat} :
    xs[*...=hi] = xs[*...(hi + 1)] := by
  simp [Std.Ric.Sliceable.mkSlice, Std.Rio.Sliceable.mkSlice]

@[simp]
public theorem toList_mkSlice_ric {xs : List α} {hi : Nat} :
    xs[*...=hi].toList = xs.take (hi + 1) := by
  rw [mkSlice_ric_eq_mkSlice_rio, toList_mkSlice_rio]

@[simp]
public theorem toArray_mkSlice_ric {xs : List α} {hi : Nat} :
    xs[*...=hi].toArray = (xs.take (hi + 1)).toArray := by
  simp [← ListSlice.toArray_toList]

public theorem toArray_mkSlice_ric' {xs : List α} {hi : Nat} :
    xs[*...=hi].toArray = xs.toArray.extract 0 (hi + 1) := by
  simp

@[simp]
public theorem size_mkSlice_ric {xs : List α} {hi : Nat} :
    xs[*...=hi].size = min (hi + 1) xs.length := by
  simp [← ListSlice.length_toList]

@[simp]
public theorem mkSlice_rii_eq_mkSlice_rci {xs : List α} :
    xs[*...*] = xs[0...*] := by
  simp [Std.Rii.Sliceable.mkSlice, Std.Rci.Sliceable.mkSlice]

@[simp]
public theorem toList_mkSlice_rii {xs : List α} :
    xs[*...*].toList = xs := by
  rw [mkSlice_rii_eq_mkSlice_rci, toList_mkSlice_rci, List.drop_zero]

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

@[simp]
public theorem toList_mkSlice_rco {xs : ListSlice α} {lo hi : Nat} :
    xs[lo...hi].toList = (xs.toList.take hi).drop lo := by
  simp [instSliceableListSliceNat_1, ListSlice.toList_eq (xs := xs)]
  obtain ⟨⟨xs, stop⟩⟩ := xs
  cases stop
  · simp
  · simp [List.take_take, Nat.min_comm]

@[simp]
public theorem mkSlice_rcc_eq_mkSlice_rco {xs : ListSlice α} {lo hi : Nat} :
    xs[lo...=hi] = xs[lo...(hi + 1)] := by
  simp [Std.Rcc.Sliceable.mkSlice, Std.Rco.Sliceable.mkSlice]

@[simp]
public theorem toList_mkSlice_rcc {xs : ListSlice α} {lo hi : Nat} :
    xs[lo...=hi].toList = (xs.toList.take (hi + 1)).drop lo := by
  rw [mkSlice_rcc_eq_mkSlice_rco, toList_mkSlice_rco]

@[simp]
public theorem toList_mkSlice_rci {xs : ListSlice α} {lo : Nat} :
    xs[lo...*].toList = xs.toList.drop lo := by
  simp only [instSliceableListSliceNat_2, ListSlice.toList_eq (xs := xs)]
  obtain ⟨⟨xs, stop⟩⟩ := xs
  simp only
  split <;> simp

@[simp]
public theorem mkSlice_roo_eq_mkSlice_rco {xs : ListSlice α} {lo hi : Nat} :
    xs[lo<...hi] = xs[(lo + 1)...hi] := by
  simp [Std.Roo.Sliceable.mkSlice, Std.Rco.Sliceable.mkSlice]

@[simp]
public theorem toList_mkSlice_roo {xs : ListSlice α} {lo hi : Nat} :
    xs[lo<...hi].toList = (xs.toList.take hi).drop (lo + 1) := by
  rw [mkSlice_roo_eq_mkSlice_rco, toList_mkSlice_rco]

@[simp]
public theorem mkSlice_roc_eq_mkSlice_roo {xs : ListSlice α} {lo hi : Nat} :
    xs[lo<...=hi] = xs[lo<...(hi + 1)] := by
  simp [Std.Roc.Sliceable.mkSlice, Std.Roo.Sliceable.mkSlice]

@[simp]
public theorem mkSlice_roc_eq_mkSlice_rcc {xs : ListSlice α} {lo hi : Nat} :
    xs[lo<...=hi] = xs[(lo + 1)...=hi] := by
  simp [Std.Roc.Sliceable.mkSlice, Std.Rco.Sliceable.mkSlice]

@[simp]
public theorem toList_mkSlice_roc {xs : ListSlice α} {lo hi : Nat} :
    xs[lo<...=hi].toList = (xs.toList.take (hi + 1)).drop (lo + 1) := by
  rw [mkSlice_roc_eq_mkSlice_rcc, toList_mkSlice_rcc]

@[simp]
public theorem mkSlice_roi_eq_mkSlice_rci {xs : ListSlice α} {lo : Nat} :
    xs[lo<...*] = xs[(lo + 1)...*] := by
  simp [Std.Roi.Sliceable.mkSlice, Std.Rci.Sliceable.mkSlice]

@[simp]
public theorem toList_mkSlice_roi {xs : ListSlice α} {lo : Nat} :
    xs[lo<...*].toList = xs.toList.drop (lo + 1) := by
  rw [mkSlice_roi_eq_mkSlice_rci, toList_mkSlice_rci]

@[simp]
public theorem mkSlice_rio_eq_mkSlice_rco {xs : ListSlice α} {hi : Nat} :
    xs[*...hi] = xs[0...hi] := by
  simp [Std.Rio.Sliceable.mkSlice, Std.Rco.Sliceable.mkSlice]

@[simp]
public theorem toList_mkSlice_rio {xs : ListSlice α} {hi : Nat} :
    xs[*...hi].toList = xs.toList.take hi := by
  rw [mkSlice_rio_eq_mkSlice_rco, toList_mkSlice_rco, List.drop_zero]

@[simp]
public theorem mkSlice_ric_eq_mkSlice_rio {xs : ListSlice α} {hi : Nat} :
    xs[*...=hi] = xs[*...(hi + 1)] := by
  simp [Std.Ric.Sliceable.mkSlice, Std.Rio.Sliceable.mkSlice]

@[simp]
public theorem mkSlice_ric_eq_mkSlice_rcc {xs : ListSlice α} {hi : Nat} :
    xs[*...=hi] = xs[0...=hi] := by
  simp [Std.Ric.Sliceable.mkSlice, Std.Rco.Sliceable.mkSlice]

@[simp]
public theorem toList_mkSlice_ric {xs : ListSlice α} {hi : Nat} :
    xs[*...=hi].toList = xs.toList.take (hi + 1) := by
  rw [mkSlice_ric_eq_mkSlice_rcc, toList_mkSlice_rcc, List.drop_zero]

@[simp]
public theorem mkSlice_rii {xs : ListSlice α} :
    xs[*...*] = xs := by
  simp [Std.Rii.Sliceable.mkSlice]

@[simp]
public theorem toList_mkSlice_rii {xs : ListSlice α} :
    xs[*...*].toList = xs.toList := by
  rw [mkSlice_rii]

end ListSlice

end ListSubslices
