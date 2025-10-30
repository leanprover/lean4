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

theorem internalIter_rco_eq {α : Type u} {s : ListSlice α} :
    Internal.iter s = s.internalRepresentation.list.iter.take s.internalRepresentation.stop := by
  simp [Internal.iter, ToIterator.iter_eq]

theorem toList_internalIter {α : Type u} {s : ListSlice α} :
    (Internal.iter s).toList = s.internalRepresentation.list.take s.internalRepresentation.stop := by
  simp [internalIter_rco_eq]

theorem internalIter_eq_toIteratorIter {α : Type u} {s : ListSlice α} :
    Internal.iter s = ToIterator.iter s :=
  rfl

public instance : LawfulSliceSize (Internal.ListSliceData α) where
  lawful s := by
    simp [← internalIter_eq_toIteratorIter, SliceSize.size]

end Std.Slice.List
