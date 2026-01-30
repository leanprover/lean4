/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Std.Data.Iterators.Producers.Slice
import all Std.Data.Iterators.Producers.Slice
public import Init.Data.Slice.Lemmas

@[expose] public section

namespace Std.Slice

open Std.Iterators

variable {γ : Type u} {α β : Type v}

theorem Internal.iter_eq_iter [ToIterator (Slice γ) Id α β] {s : Slice γ} :
    s.iter = Internal.iter s :=
  (rfl)

theorem iter_eq_toIteratorIter {γ : Type u} {s : Slice γ}
    [ToIterator (Slice γ) Id α β] :
    s.iter = ToIterator.iter s := by
  simp [Internal.iter_eq_iter, Internal.iter_eq_toIteratorIter]

theorem size_eq_count_iter [ToIterator (Slice γ) Id α β]
    [Iterator α Id β] {s : Slice γ}
    [Finite α Id]
    [IteratorLoop α Id Id] [LawfulIteratorLoop α Id Id]
    [SliceSize γ] [LawfulSliceSize γ] :
    s.size = s.iter.count := by
  simp [Internal.iter_eq_iter, Internal.size_eq_count_iter]

theorem count_iter_eq_size [ToIterator (Slice γ) Id α β]
    [Iterator α Id β] {s : Slice γ}
    [Finite α Id]
    [IteratorLoop α Id Id] [LawfulIteratorLoop α Id Id]
    [SliceSize γ] [LawfulSliceSize γ] :
    s.iter.count = s.size :=
  size_eq_count_iter.symm

@[simp]
theorem toArray_iter {s : Slice γ} [ToIterator (Slice γ) Id α β]
    [Iterator α Id β]
    [Finite α Id] :
    s.iter.toArray = s.toArray := by
  simp [Internal.iter_eq_iter, Internal.toArray_eq_toArray_iter]

@[deprecated toArray_iter (since := "2025-11-13")]
theorem toArray_eq_toArray_iter {s : Slice γ} [ToIterator (Slice γ) Id α β]
    [Iterator α Id β]
    [Finite α Id] :
    s.toArray = s.iter.toArray := by
  simp

@[simp]
theorem toList_iter {s : Slice γ} [ToIterator (Slice γ) Id α β]
    [Iterator α Id β]
    [Finite α Id] :
    s.iter.toList = s.toList := by
  simp [Internal.iter_eq_iter, Internal.toList_eq_toList_iter]

@[deprecated toList_iter (since := "2025-11-13")]
theorem toList_eq_toList_iter {s : Slice γ} [ToIterator (Slice γ) Id α β]
    [Iterator α Id β]
    [Finite α Id] :
    s.toList = s.iter.toList := by
  simp

@[simp]
theorem toListRev_iter {s : Slice γ} [ToIterator (Slice γ) Id α β]
    [Iterator α Id β] [Finite α Id] :
    s.iter.toListRev = s.toListRev := by
  simp [Internal.iter_eq_iter, Internal.toListRev_eq_toListRev_iter]

@[deprecated toListRev_iter (since := "2025-11-13")]
theorem toListRev_eq_toListRev_iter {s : Slice γ} [ToIterator (Slice γ) Id α β]
    [Iterator α Id β] [Finite α Id] :
    s.toListRev = s.iter.toListRev := by
  simp

end Std.Slice
