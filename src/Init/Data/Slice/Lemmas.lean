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

public section

namespace Std.Slice

open Std.Iterators

variable {γ : Type u} {β : Type v}

theorem Internal.iter_eq_toIteratorIter {γ : Type u} {s : Slice γ}
    [ToIterator s Id β] :
    Internal.iter s = ToIterator.iter s :=
  (rfl)

theorem Internal.size_eq_count_iter [∀ s : Slice γ, ToIterator s Id β]
    [∀ s : Slice γ, Iterator (ToIterator.State s Id) Id β] {s : Slice γ}
    [Finite (ToIterator.State s Id) Id]
    [IteratorLoop (ToIterator.State s Id) Id Id] [LawfulIteratorLoop (ToIterator.State s Id) Id Id]
    [SliceSize γ] [LawfulSliceSize γ] :
    s.size = (Internal.iter s).count := by
  letI : IteratorCollect (ToIterator.State s Id) Id Id := .defaultImplementation
  simp only [Slice.size, iter, LawfulSliceSize.lawful, ← Iter.length_toList_eq_count]

theorem Internal.toArray_eq_toArray_iter {s : Slice γ} [ToIterator s Id β]
    [Iterator (ToIterator.State s Id) Id β] [IteratorCollect (ToIterator.State s Id) Id Id]
    [Finite (ToIterator.State s Id) Id] :
    s.toArray = (Internal.iter s).toArray :=
  (rfl)

theorem Internal.toList_eq_toList_iter {s : Slice γ} [ToIterator s Id β]
    [Iterator (ToIterator.State s Id) Id β] [IteratorCollect (ToIterator.State s Id) Id Id]
    [Finite (ToIterator.State s Id) Id] :
    s.toList = (Internal.iter s).toList :=
  (rfl)

theorem Internal.toListRev_eq_toListRev_iter {s : Slice γ} [ToIterator s Id β]
    [Iterator (ToIterator.State s Id) Id β] [Finite (ToIterator.State s Id) Id] :
    s.toListRev = (Internal.iter s).toListRev :=
  (rfl)

@[simp]
theorem size_toArray_eq_size [∀ s : Slice γ, ToIterator s Id β]
    [∀ s : Slice γ, Iterator (ToIterator.State s Id) Id β] {s : Slice γ}
    [SliceSize γ] [LawfulSliceSize γ]
    [IteratorCollect (ToIterator.State s Id) Id Id] [Finite (ToIterator.State s Id) Id]
    [LawfulIteratorCollect (ToIterator.State s Id) Id Id] :
    s.toArray.size = s.size := by
  letI : IteratorLoop (ToIterator.State s Id) Id Id := .defaultImplementation
  rw [Internal.size_eq_count_iter, Internal.toArray_eq_toArray_iter, Iter.size_toArray_eq_count]

@[simp]
theorem length_toList_eq_size [∀ s : Slice γ, ToIterator s Id β]
    [∀ s : Slice γ, Iterator (ToIterator.State s Id) Id β] {s : Slice γ}
    [SliceSize γ] [LawfulSliceSize γ] [IteratorCollect (ToIterator.State s Id) Id Id]
    [Finite (ToIterator.State s Id) Id] [LawfulIteratorCollect (ToIterator.State s Id) Id Id] :
    s.toList.length = s.size := by
  letI : IteratorLoop (ToIterator.State s Id) Id Id := .defaultImplementation
  rw [Internal.size_eq_count_iter, Internal.toList_eq_toList_iter, Iter.length_toList_eq_count]

@[simp]
theorem length_toListRev_eq_size [∀ s : Slice γ, ToIterator s Id β]
    [∀ s : Slice γ, Iterator (ToIterator.State s Id) Id β] {s : Slice γ}
    [IteratorLoop (ToIterator.State s Id) Id Id.{v}] [SliceSize γ] [LawfulSliceSize γ]
    [Finite (ToIterator.State s Id) Id]
    [LawfulIteratorLoop (ToIterator.State s Id) Id Id] :
    s.toListRev.length = s.size := by
  letI : IteratorCollect (ToIterator.State s Id) Id Id := .defaultImplementation
  rw [Internal.size_eq_count_iter, Internal.toListRev_eq_toListRev_iter,
    Iter.length_toListRev_eq_count]

end Std.Slice
