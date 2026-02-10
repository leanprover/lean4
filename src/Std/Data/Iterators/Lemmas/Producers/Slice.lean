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
import Init.Data.Slice.InternalLemmas

public section

namespace Std.Slice

open Std.Iterators

variable {γ : Type u} {α β : Type v}

theorem Internal.iter_eq_internalIter [ToIterator (Slice γ) Id α β] {s : Slice γ} :
    s.iter = Internal.iter s :=
  (rfl)

theorem iter_eq_toIteratorIter {γ : Type u} {s : Slice γ}
    [ToIterator (Slice γ) Id α β] :
    s.iter = ToIterator.iter s := by
  simp [Internal.iter_eq_internalIter, Internal.iter_eq_toIteratorIter]

theorem size_eq_length_iter [ToIterator (Slice γ) Id α β]
    [Iterator α Id β] {s : Slice γ}
    [Finite α Id]
    [IteratorLoop α Id Id] [LawfulIteratorLoop α Id Id]
    [SliceSize γ] [LawfulSliceSize γ] :
    s.size = s.iter.length := by
  simp [Internal.iter_eq_internalIter, Internal.size_eq_length_internalIter]

@[deprecated size_eq_length_iter (since := "2026-01-28")]
def size_eq_count_iter := @size_eq_length_iter

theorem length_iter_eq_size [ToIterator (Slice γ) Id α β]
    [Iterator α Id β] {s : Slice γ}
    [Finite α Id]
    [IteratorLoop α Id Id] [LawfulIteratorLoop α Id Id]
    [SliceSize γ] [LawfulSliceSize γ] :
    s.iter.length = s.size :=
  size_eq_length_iter.symm

@[deprecated length_iter_eq_size (since := "2026-01-28")]
def count_iter_eq_size := @length_iter_eq_size

@[simp]
theorem toArray_iter {s : Slice γ} [ToIterator (Slice γ) Id α β]
    [Iterator α Id β]
    [Finite α Id] :
    s.iter.toArray = s.toArray := by
  simp [Internal.iter_eq_internalIter, Internal.toArray_eq_toArray_internalIter]

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
  simp [Internal.iter_eq_internalIter, Internal.toList_eq_toList_internalIter]

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
  simp [Internal.iter_eq_internalIter, Internal.toListRev_eq_toListRev_internalIter]

@[deprecated toListRev_iter (since := "2025-11-13")]
theorem toListRev_eq_toListRev_iter {s : Slice γ} [ToIterator (Slice γ) Id α β]
    [Iterator α Id β] [Finite α Id] :
    s.toListRev = s.iter.toListRev := by
  simp

theorem forIn_iter {β : Type v}
    {m : Type w → Type x} [Monad m] {δ : Type w}
    [ToIterator (Slice γ) Id α β]
    [Iterator α Id β]
    [IteratorLoop α Id m]
    [LawfulIteratorLoop α Id m]
    [Finite α Id] {s : Slice γ}
    {init : δ} {f : β → δ → m (ForInStep δ)} :
    ForIn.forIn s.iter init f = ForIn.forIn s init f := by
  simp [Internal.iter_eq_internalIter, forIn_internalIter]

theorem fold_iter [ToIterator (Slice γ) Id α β]
    [Iterator α Id β] [IteratorLoop α Id Id] [Iterators.Finite α Id] {s : Slice γ} :
    s.iter.fold (init := init) f = s.foldl (init := init) f := by
  simp [Internal.iter_eq_internalIter, fold_internalIter]

theorem foldM_iter {m : Type w → Type w'} [Monad m] [ToIterator (Slice γ) Id α β]
    [Iterator α Id β] [IteratorLoop α Id m] [Iterators.Finite α Id] {s : Slice γ} {f : δ → β → m δ} :
    s.iter.foldM (init := init) f = s.foldlM (init := init) f := by
  simp [Internal.iter_eq_internalIter, foldM_internalIter]

end Std.Slice
