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

variable {γ : Type u} {β : Type v}

theorem Internal.iter_eq_iter {s : Slice γ} [ToIterator s Id β] :
    s.iter = Internal.iter s :=
  (rfl)

theorem iter_eq_toIteratorIter {γ : Type u} {s : Slice γ}
    [ToIterator s Id β] :
    s.iter = ToIterator.iter s := by
  simp [Internal.iter_eq_iter, Internal.iter_eq_toIteratorIter]

theorem size_eq_size_iter {s : Slice γ} [ToIterator s Id β]
    [Iterator (ToIterator.State s Id) Id β] [IteratorSize (ToIterator.State s Id) Id] :
    s.size = s.iter.size := by
  simp [Internal.iter_eq_iter, Internal.size_eq_size_iter]

theorem toArray_eq_toArray_iter {s : Slice γ} [ToIterator s Id β]
    [Iterator (ToIterator.State s Id) Id β] [IteratorCollect (ToIterator.State s Id) Id Id]
    [Finite (ToIterator.State s Id) Id] :
    s.toArray = s.iter.toArray := by
  simp [Internal.iter_eq_iter, Internal.toArray_eq_toArray_iter]

theorem toList_eq_toList_iter {s : Slice γ} [ToIterator s Id β]
    [Iterator (ToIterator.State s Id) Id β] [IteratorCollect (ToIterator.State s Id) Id Id]
    [Finite (ToIterator.State s Id) Id] :
    s.toList = s.iter.toList := by
  simp [Internal.iter_eq_iter, Internal.toList_eq_toList_iter]

theorem toListRev_eq_toListRev_iter {s : Slice γ} [ToIterator s Id β]
    [Iterator (ToIterator.State s Id) Id β] [Finite (ToIterator.State s Id) Id] :
    s.toListRev = s.iter.toListRev := by
  simp [Internal.iter_eq_iter, Internal.toListRev_eq_toListRev_iter]

end Std.Slice
