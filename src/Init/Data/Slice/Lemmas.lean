/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Slice.Operations
import all Init.Data.Slice.Operations
import Init.Data.Iterators.Lemmas.Consumers
public import Init.Data.List.Control
public import Init.Data.Iterators.Consumers.Collect

import Init.Data.Slice.InternalLemmas

open Std Std.Iterators

namespace Std.Slice

variable {γ : Type u} {α β : Type v}

@[simp]
public theorem forIn_toList {γ : Type u} {β : Type v}
    {m : Type w → Type x} [Monad m] [LawfulMonad m] {δ : Type w}
    [ToIterator (Slice γ) Id α β]
    [Iterator α Id β]
    [IteratorLoop α Id m]
    [LawfulIteratorLoop α Id m]
    [Finite α Id] {s : Slice γ}
    {init : δ} {f : β → δ → m (ForInStep δ)} :
    ForIn.forIn s.toList init f = ForIn.forIn s init f := by
  rw [← forIn_internalIter, ← Iter.forIn_toList, Slice.toList]

@[simp]
public theorem forIn_toArray {γ : Type u} {β : Type v}
    {m : Type w → Type x} [Monad m] [LawfulMonad m] {δ : Type w}
    [ToIterator (Slice γ) Id α β]
    [Iterator α Id β]
    [IteratorLoop α Id m]
    [LawfulIteratorLoop α Id m]
    [Finite α Id] {s : Slice γ}
    {init : δ} {f : β → δ → m (ForInStep δ)} :
    ForIn.forIn s.toArray init f = ForIn.forIn s init f := by
  rw [← forIn_internalIter, ← Iter.forIn_toArray, Slice.toArray]

@[simp, grind =, suggest_for ListSlice.size_toArray ListSlice.size_toArray_eq_size]
public theorem size_toArray_eq_size [ToIterator (Slice γ) Id α β]
    [Iterator α Id β] [SliceSize γ] [LawfulSliceSize γ]
    [Finite α Id]
    {s : Slice γ} :
    s.toArray.size = s.size := by
  letI : IteratorLoop α Id Id := .defaultImplementation
  rw [Internal.size_eq_length_internalIter, Internal.toArray_eq_toArray_internalIter, Iter.size_toArray_eq_length]

@[simp, grind =, suggest_for ListSlice.length_toList ListSlice.length_toList_eq_size]
public theorem length_toList_eq_size [ToIterator (Slice γ) Id α β]
    [Iterator α Id β] {s : Slice γ}
    [SliceSize γ] [LawfulSliceSize γ]
    [Finite α Id] :
    s.toList.length = s.size := by
  letI : IteratorLoop α Id Id := .defaultImplementation
  rw [Internal.size_eq_length_internalIter, Internal.toList_eq_toList_internalIter, Iter.length_toList_eq_length]

@[simp, grind =]
public theorem length_toListRev_eq_size [ToIterator (Slice γ) Id α β]
    [Iterator α Id β] {s : Slice γ}
    [IteratorLoop α Id Id.{v}] [SliceSize γ] [LawfulSliceSize γ]
    [Finite α Id]
    [LawfulIteratorLoop α Id Id] :
    s.toListRev.length = s.size := by
  rw [Internal.size_eq_length_internalIter, Internal.toListRev_eq_toListRev_internalIter,
    Iter.length_toListRev_eq_length]

public theorem foldlM_toList {m} [Monad m] [ToIterator (Slice γ) Id α β]
    [Iterator α Id β] [LawfulMonad m] [IteratorLoop α Id m] [LawfulIteratorLoop α Id m]
    [Iterators.Finite α Id] {s : Slice γ} {f} :
    s.toList.foldlM (init := init) f = s.foldlM (m := m) (init := init) f := by
  simp [Internal.toList_eq_toList_internalIter, Iter.foldlM_toList, foldM_internalIter]

public theorem foldl_toList [ToIterator (Slice γ) Id α β]
    [Iterator α Id β] [IteratorLoop α Id Id] [LawfulIteratorLoop α Id Id]
    [Iterators.Finite α Id] {s : Slice γ} :
    s.toList.foldl (init := init) f = s.foldl (init := init) f := by
  simp [Internal.toList_eq_toList_internalIter, Iter.foldl_toList, fold_internalIter]

end Std.Slice
