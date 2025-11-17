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

theorem ListSlice.toList_eq {xs : ListSlice α} :
    xs.toList = match xs.internalRepresentation.stop with
      | some stop => xs.internalRepresentation.list.take stop
      | none => xs.internalRepresentation.list := by
  simp only [toList, List.ofSlice, Std.Slice.toList, ToIterator.state_eq]
  rw [Std.Slice.List.toList_internalIter]

public theorem List.rccSlice.toList_eq {xs : List α} {lo hi : Nat} :
  xs[lo...=hi].toList = (xs.take (hi + 1)).drop lo := by
    by_cases lo ≤ hi + 1
    · simp [ListSlice.toList_eq, Std.Rcc.Sliceable.mkSlice, List.toSlice, *, List.take_drop]
    · simp [ListSlice.toList_eq, Std.Rcc.Sliceable.mkSlice, List.toSlice, *]
      omega
