/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Slice.Basic
public import Init.Data.Slice.Notation
public import Init.Data.Iterators.ToIterator

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
def size (s : Slice γ) [ToIterator s Id β] [Iterator (ToIterator.State s Id) Id β]
    [IteratorSize (ToIterator.State s Id) Id] :=
  Internal.iter s |>.size

/-- Allocates a new array that contains the elements of the slice. -/
@[always_inline, inline]
def toArray (s : Slice γ) [ToIterator s Id β] [Iterator (ToIterator.State s Id) Id β]
    [IteratorCollect (ToIterator.State s Id) Id Id] [Finite (ToIterator.State s Id) Id] : Array β :=
  Internal.iter s |>.toArray

/-- Allocates a new list that contains the elements of the slice. -/
@[always_inline, inline]
def toList (s : Slice γ) [ToIterator s Id β] [Iterator (ToIterator.State s Id) Id β]
    [IteratorCollect (ToIterator.State s Id) Id Id] [Finite (ToIterator.State s Id) Id] : List β :=
  Internal.iter s |>.toList

/-- Allocates a new list that contains the elements of the slice in reverse order. -/
@[always_inline, inline]
def toListRev (s : Slice γ) [ToIterator s Id β] [Iterator (ToIterator.State s Id) Id β]
    [Finite (ToIterator.State s Id) Id] : List β :=
  Internal.iter s |>.toListRev

/--
Folds a monadic operation from left to right over the elements in a slice.
An accumulator of type `β` is constructed by starting with `init` and monadically combining each
element of the slice with the current accumulator value in turn. The monad in question may permit
early termination or repetition.

Examples for the special case of subarrays:
```lean example
#eval #["red", "green", "blue"].toSubarray.foldlM (init := "") fun acc x => do
  let l ← Option.guard (· ≠ 0) x.length
  return s!"{acc}({l}){x} "
```
```output
some "(3)red (5)green (4)blue "
```
```lean example
#eval #["red", "green", "blue"].toSubarray.foldlM (init := 0) fun acc x => do
  let l ← Option.guard (· ≠ 5) x.length
  return s!"{acc}({l}){x} "
```
```output
none
```
-/
@[always_inline, inline]
def foldlM {γ : Type u} {β : Type v}
    {δ : Type w} {m : Type w → Type w'} [Monad m] (f : δ → β → m δ) (init : δ)
    (s : Slice γ) [ToIterator s Id β] [Iterator (ToIterator.State s Id) Id β]
    [IteratorLoop (ToIterator.State s Id) Id m] [Finite (ToIterator.State s Id) Id] : m δ :=
  Internal.iter s |>.foldM f init

/--
Folds an operation from left to right over the elements in a slice.
An accumulator of type `β` is constructed by starting with `init` and combining each
element of the slice with the current accumulator value in turn.
Examples for the special case of subarrays:
 * `#["red", "green", "blue"].toSubarray.foldl (· + ·.length) 0 = 12`
 * `#["red", "green", "blue"].toSubarray.popFront.foldl (· + ·.length) 0 = 9`
-/
@[always_inline, inline]
def foldl {γ : Type u} {β : Type v}
    {δ : Type w} (f : δ → β → δ) (init : δ)
    (s : Slice γ) [ToIterator s Id β] [Iterator (ToIterator.State s Id) Id β]
    [IteratorLoop (ToIterator.State s Id) Id Id] [Finite (ToIterator.State s Id) Id] : δ :=
  Internal.iter s |>.fold f init

end Std.Slice
