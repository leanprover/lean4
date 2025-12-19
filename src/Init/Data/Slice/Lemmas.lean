/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Slice.Operations
import all Init.Data.Slice.Operations
import Init.Data.Iterators.Consumers
import Init.Data.Iterators.Lemmas.Consumers
public import Init.Data.List.Control

public section

namespace Std.Slice

open Std.Iterators

variable {γ : Type u} {α β : Type v}

theorem Internal.iter_eq_toIteratorIter {γ : Type u}
    [ToIterator (Slice γ) Id α β] {s : Slice γ} :
    Internal.iter s = ToIterator.iter s :=
  (rfl)

theorem forIn_internalIter {γ : Type u} {β : Type v}
    {m : Type w → Type x} [Monad m] {δ : Type w}
    [ToIterator (Slice γ) Id α β]
    [Iterator α Id β]
    [IteratorLoop α Id m]
    [LawfulIteratorLoop α Id m]
    [Finite α Id] {s : Slice γ}
    {init : δ} {f : β → δ → m (ForInStep δ)} :
    ForIn.forIn (Internal.iter s) init f = ForIn.forIn s init f :=
  (rfl)

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

theorem Internal.size_eq_count_iter [ToIterator (Slice γ) Id α β]
    [Iterator α Id β] [Finite α Id]
    [IteratorLoop α Id Id] [LawfulIteratorLoop α Id Id]
    {s : Slice γ} [SliceSize γ] [LawfulSliceSize γ] :
    s.size = (Internal.iter s).count := by
  simp only [Slice.size, iter, LawfulSliceSize.lawful, ← Iter.length_toList_eq_count]

theorem Internal.toArray_eq_toArray_iter {s : Slice γ} [ToIterator (Slice γ) Id α β]
    [Iterator α Id β]
    [Finite α Id] :
    s.toArray = (Internal.iter s).toArray :=
  (rfl)

theorem Internal.toList_eq_toList_iter {s : Slice γ} [ToIterator (Slice γ) Id α β]
    [Iterator α Id β]
    [Finite α Id] :
    s.toList = (Internal.iter s).toList :=
  (rfl)

theorem Internal.toListRev_eq_toListRev_iter {s : Slice γ} [ToIterator (Slice γ) Id α β]
    [Iterator α Id β] [Finite α Id] :
    s.toListRev = (Internal.iter s).toListRev :=
  (rfl)

@[simp]
theorem size_toArray_eq_size [ToIterator (Slice γ) Id α β]
    [Iterator α Id β] [SliceSize γ] [LawfulSliceSize γ]
    [Finite α Id]
    {s : Slice γ} :
    s.toArray.size = s.size := by
  letI : IteratorLoop α Id Id := .defaultImplementation
  rw [Internal.size_eq_count_iter, Internal.toArray_eq_toArray_iter, Iter.size_toArray_eq_count]

@[simp]
theorem length_toList_eq_size [ToIterator (Slice γ) Id α β]
    [Iterator α Id β] {s : Slice γ}
    [SliceSize γ] [LawfulSliceSize γ]
    [Finite α Id] :
    s.toList.length = s.size := by
  letI : IteratorLoop α Id Id := .defaultImplementation
  rw [Internal.size_eq_count_iter, Internal.toList_eq_toList_iter, Iter.length_toList_eq_count]

@[simp]
theorem length_toListRev_eq_size [ToIterator (Slice γ) Id α β]
    [Iterator α Id β] {s : Slice γ}
    [IteratorLoop α Id Id.{v}] [SliceSize γ] [LawfulSliceSize γ]
    [Finite α Id]
    [LawfulIteratorLoop α Id Id] :
    s.toListRev.length = s.size := by
  rw [Internal.size_eq_count_iter, Internal.toListRev_eq_toListRev_iter,
    Iter.length_toListRev_eq_count]

end Std.Slice
