/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Slice.Basic
public import Init.Data.Slice.Notation
public import Init.Data.Iterators

public section

open Std.Iterators

namespace Std.Slice

instance {x : γ} [ToIterator x m β] : ToIterator (Slice.mk x) m β where
  State := ToIterator.State x m
  iterMInternal := ToIterator.iterMInternal

/--
Internal function to obtain an iterator from a slice. Users should import `Std.Data.Iterators`
and use `Std.Slice.iter` instead.
-/
@[always_inline, inline]
def Internal.iter (s : Slice γ) [ToIterator s Id β] :=
  ToIterator.iter s

/--
Returns the number of elements with distinct indices in the given slice.

Example: `#[1, 1, 1][0...2].size = 2`.
-/
@[always_inline, inline]
def size (s : Slice g) [ToIterator s Id β] [Iterator (ToIterator.State s Id) Id β]
    [IteratorSize (ToIterator.State s Id) Id] :=
  Internal.iter s |>.size

/-- Allocates a new array that contains the elements of the slice. -/
@[always_inline, inline]
def toArray (s : Slice g) [ToIterator s Id β] [Iterator (ToIterator.State s Id) Id β]
    [IteratorCollect (ToIterator.State s Id) Id Id] [Finite (ToIterator.State s Id) Id] : Array β :=
  Internal.iter s |>.toArray

/-- Allocates a new list that contains the elements of the slice. -/
@[always_inline, inline]
def toList (s : Slice g) [ToIterator s Id β] [Iterator (ToIterator.State s Id) Id β]
    [IteratorCollect (ToIterator.State s Id) Id Id] [Finite (ToIterator.State s Id) Id] : List β :=
  Internal.iter s |>.toList

/-- Allocates a new list that contains the elements of the slice in reverse order. -/
@[always_inline, inline]
def toListRev (s : Slice g) [ToIterator s Id β] [Iterator (ToIterator.State s Id) Id β]
    [Finite (ToIterator.State s Id) Id] : List β :=
  Internal.iter s |>.toListRev

end Std.Slice
