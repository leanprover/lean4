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

instance [ToIterator γ m α β] : ToIterator (Slice γ) m α β where
  iterMInternal x := ToIterator.iterMInternal x.internalRepresentation

/--
Internal function to obtain an iterator from a slice. Users should import `Std.Data.Iterators`
and use `Std.Slice.iter` instead.
-/
@[always_inline, inline]
def Internal.iter [ToIterator (Slice γ) Id α β] (s : Slice γ) :=
  ToIterator.iter s

/--
This type class provides support for the `Slice.size` function.
-/
class SliceSize (γ : Type u) where
  /-- Computes the slice of a `Slice`. Use `Slice.size` instead. -/
  size (slice : Slice γ) : Nat

/--
This type class states that the slice's iterator emits exactly `Slice.size` elements before
terminating.
-/
class LawfulSliceSize (γ : Type u) [SliceSize γ] [ToIterator (Slice γ) Id α β]
    [Iterator α Id β] where
  /-- The iterator for every `Slice α` is finite. -/
  [finite : Finite α Id]
  /-- The iterator of a slice `s` of type `Slice γ` emits exactly `SliceSize.size s` elements. -/
  lawful :
      letI : IteratorLoop α Id Id := .defaultImplementation
      ∀ s : Slice γ, SliceSize.size s = (ToIterator.iter (γ := Slice γ) s).count

/--
Returns the number of elements with distinct indices in the given slice.

Example: `#[1, 1, 1][0...2].size = 2`.
-/
@[always_inline, inline]
def size (s : Slice γ) [SliceSize γ] :=
  SliceSize.size s

/-- Allocates a new array that contains the elements of the slice. -/
@[always_inline, inline]
def toArray [ToIterator (Slice γ) Id α β] [Iterator α Id β]
    [Finite α Id] (s : Slice γ) : Array β :=
  Internal.iter s |>.toArray

/-- Allocates a new list that contains the elements of the slice. -/
@[always_inline, inline]
def toList [ToIterator (Slice γ) Id α β] [Iterator α Id β]
    [Finite α Id]
    (s : Slice γ) : List β :=
  Internal.iter s |>.toList

/-- Allocates a new list that contains the elements of the slice in reverse order. -/
@[always_inline, inline]
def toListRev [ToIterator (Slice γ) Id α β] [Iterator α Id β]
    [Finite α Id] (s : Slice γ) : List β :=
  Internal.iter s |>.toListRev

instance {γ : Type u} {β : Type v} [Monad m] [ToIterator (Slice γ) Id α β]
    [Iterator α Id β]
    [IteratorLoop α Id m]
    [Finite α Id] :
    ForIn m (Slice γ) β where
  forIn s init f :=
    forIn (Internal.iter s) init f

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
    [ToIterator (Slice γ) Id α β] [Iterator α Id β]
    [IteratorLoop α Id m] [Finite α Id]
    (s : Slice γ) : m δ :=
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
    [ToIterator (Slice γ) Id α β] [Iterator α Id β]
    [IteratorLoop α Id Id] [Finite α Id]
    (s : Slice γ) : δ :=
  Internal.iter s |>.fold f init

end Std.Slice
