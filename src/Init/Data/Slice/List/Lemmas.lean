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



-- public theorem List.rccSlice.toList_eq {xs : List α} {lo hi : Nat} :
--   xs[lo...=hi].toList = (xs.take (hi + 1)).drop lo := by
--     by_cases lo ≤ hi + 1
--     · simp [ListSlice.toList_eq, Std.Rcc.Sliceable.mkSlice, List.toSlice, *, List.take_drop]
--     · simp [ListSlice.toList_eq, Std.Rcc.Sliceable.mkSlice, List.toSlice, *]
--       omega

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
public theorem mkSlice_rcc_eq_mkSlice_rco {xs : List α} {lo hi : Nat} :
    xs[lo...=hi] = xs[lo...(hi + 1)] := by
  simp [Std.Rcc.Sliceable.mkSlice, Std.Rco.Sliceable.mkSlice]

@[simp]
public theorem toList_mkSlice_rcc {xs : List α} {lo hi : Nat} :
    xs[lo...=hi].toList = (xs.take (hi + 1)).drop lo := by
  rw [mkSlice_rcc_eq_mkSlice_rco, toList_mkSlice_rco]

@[simp]
public theorem toList_mkSlice_rci {xs : List α} {lo : Nat} :
    xs[lo...*].toList = xs.drop lo := by
  rw [List.drop_eq_drop_min]
  simp [ListSlice.toList_eq, Std.Rci.Sliceable.mkSlice, List.toUnboundedSlice]

@[simp]
public theorem mkSlice_roo_eq_mkSlice_rco {xs : List α} {lo hi : Nat} :
    xs[lo<...hi] = xs[(lo + 1)...hi] := by
  simp [Std.Roo.Sliceable.mkSlice, Std.Rco.Sliceable.mkSlice]

@[simp]
public theorem toList_mkSlice_roo {xs : List α} {lo hi : Nat} :
    xs[lo<...hi].toList = (xs.take hi).drop (lo + 1) := by
  rw [mkSlice_roo_eq_mkSlice_rco, toList_mkSlice_rco]

@[simp]
public theorem mkSlice_roc_eq_mkSlice_roo {xs : List α} {lo hi : Nat} :
    xs[lo<...=hi] = xs[lo<...(hi + 1)] := by
  simp [Std.Roc.Sliceable.mkSlice, Std.Roo.Sliceable.mkSlice]

@[simp]
public theorem toList_mkSlice_roc {xs : List α} {lo hi : Nat} :
    xs[lo<...=hi].toList = (xs.take (hi + 1)).drop (lo + 1) := by
  rw [mkSlice_roc_eq_mkSlice_roo, toList_mkSlice_roo]

@[simp]
public theorem mkSlice_roi_eq_mkSlice_rci {xs : List α} {lo : Nat} :
    xs[lo<...*] = xs[(lo + 1)...*] := by
  simp [Std.Roi.Sliceable.mkSlice, Std.Rci.Sliceable.mkSlice]

@[simp]
public theorem toList_mkSlice_roi {xs : List α} {lo : Nat} :
    xs[lo<...*].toList = xs.drop (lo + 1) := by
  rw [mkSlice_roi_eq_mkSlice_rci, toList_mkSlice_rci]

end List
