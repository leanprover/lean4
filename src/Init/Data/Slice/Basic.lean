/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
import Init.Data.Range.Polymorphic

open Std.PRange
open Std.Iterators

namespace Std.Slice

/--
This marker typeclass signifies that the type `α` supports slice notation with index type `β`.
The slices contain elements of type `γ`.
-/
class Sliceable (shape : RangeShape) (α : Type u) (β : outParam (Type v))
    (γ : outParam (Type w)) where

structure _root_.Std.Slice (shape : RangeShape) (α : Type u) {β : Type v}
    {γ : Type w} [Sliceable shape α β γ] where
  carrier : α
  range : PRange shape β

macro_rules
  | `($c[*...*]) => `(Slice.mk $c *...*)
  | `($c[$a...*]) => `(Slice.mk $c $a...*)
  | `($c[$a<...*]) => `(Slice.mk $c $a...*)
  | `($c[*...<$b]) => `(Slice.mk $c *...<$b)
  | `($c[$a...<$b]) => `(Slice.mk $c $a...<$b)
  | `($c[$a<...<$b]) => `(Slice.mk $c $a...<$b)
  | `($c[*...$b]) => `(Slice.mk $c *...<$b)
  | `($c[$a...$b]) => `(Slice.mk $c $a...<$b)
  | `($c[$a<...$b]) => `(Slice.mk $c $a...<$b)
  | `($c[*...=$b]) => `(Slice.mk $c *...=$b)
  | `($c[$a...=$b]) => `(Slice.mk $c $a...=$b)
  | `($c[$a<...=$b]) => `(Slice.mk $c $a...=$b)

/-- This typeclass provides iterator support for slices of the given type and shape. -/
class SliceIter (shape : RangeShape) (α : Type u) {β : Type v} {γ : Type w}
    [Sliceable shape α β γ] where
  State : Slice shape α → Type w
  iter (slice : Slice shape α) : Iter (α := State slice) γ

@[always_inline, inline, expose]
def SliceIter.of [Sliceable shape α β γ] (State : Slice shape α → Type u)
    (iter : (slice : Slice shape α) → Iter (α := State slice) γ) :
    SliceIter shape α where
  State := State
  iter := iter

instance {shape : RangeShape} {α : Type u} {β : Type v} {γ : Type w}
    [Sliceable shape α β γ] {slice : Slice shape α} {State : Slice shape α → Type w} {iter}
    [Iterator (α := State slice) Id γ] :
    letI i : SliceIter shape α := .of State iter
    Iterator (α := i.State slice) Id γ :=
  inferInstanceAs <| Iterator (α := State slice) Id γ

instance {shape : RangeShape} {α : Type u} {β : Type v} {γ : Type w}
    [Sliceable shape α β γ] {slice : Slice shape α} {State : Slice shape α → Type w} {iter}
    [Iterator (α := State slice) Id γ] [Finite (α := State slice) Id] :
    letI i : SliceIter shape α := .of State iter
    Finite (α := i.State slice) Id :=
  inferInstanceAs <| Finite (α := State slice) Id

instance {shape : RangeShape} {α : Type u} {β : Type v} {γ : Type w} {m} [Monad m]
    [Sliceable shape α β γ] {slice : Slice shape α} {State : Slice shape α → Type w} {iter}
    [Iterator (α := State slice) Id γ] [IteratorCollect (α := State slice) Id m] :
    letI i : SliceIter shape α := .of State iter
    IteratorCollect (α := i.State slice) Id m :=
  inferInstanceAs <| IteratorCollect (α := State slice) Id m

instance {shape : RangeShape} {α : Type u} {β : Type v} {γ : Type w} {m} [Monad m]
    [Sliceable shape α β γ] {slice : Slice shape α} {State : Slice shape α → Type w} {iter}
    [Iterator (α := State slice) Id γ] [IteratorCollectPartial (α := State slice) Id m] :
    letI i : SliceIter shape α := .of State iter
    IteratorCollectPartial (α := i.State slice) Id m :=
  inferInstanceAs <| IteratorCollectPartial (α := State slice) Id m

instance {shape : RangeShape} {α : Type u} {β : Type v} {γ : Type w}
    [Sliceable shape α β γ] {slice : Slice shape α} {State : Slice shape α → Type w} {iter}
    [Iterator (α := State slice) Id γ] [IteratorSize (α := State slice) Id] :
    letI i : SliceIter shape α := .of State iter
    IteratorSize (α := i.State slice) Id :=
  inferInstanceAs <| IteratorSize (α := State slice) Id

instance {shape : RangeShape} {α : Type u} {β : Type v} {γ : Type w}
    [Sliceable shape α β γ] {slice : Slice shape α} {State : Slice shape α → Type w} {iter}
    [Iterator (α := State slice) Id γ] [IteratorSizePartial (α := State slice) Id] :
    letI i : SliceIter shape α := .of State iter
    IteratorSizePartial (α := i.State slice) Id :=
  inferInstanceAs <| IteratorSizePartial (α := State slice) Id

/--
Internal function to obtain an iterator from a slice. Users should import `Std.Data.Iterators`
and use `Std.Slice.iter` instead.
-/
@[always_inline, inline]
def Internal.iter {shape} {α : Type u} {β : Type v} {γ : Type w} [Sliceable shape α β γ]
    [i : SliceIter shape α] (s : Slice shape α) :=
  i.iter s

/--
Returns the number of elements -- not necessarily distinct -- in the given slice.
-/
@[always_inline, inline]
def size {shape} {α : Type u} {β : Type v} {γ : Type w} [Sliceable shape α β γ]
    [i : SliceIter shape α] (s : Slice shape α) [Iterator (i.State s) Id γ]
    [IteratorSize (i.State s) Id] :=
  Internal.iter s |>.size

@[always_inline, inline]
def toArray {shape} {α : Type u} {β : Type v} {γ : Type w} [Sliceable shape α β γ]
    [i : SliceIter shape α] (s : Slice shape α) [Iterator (i.State s) Id γ]
    [Finite (i.State s) Id] [IteratorCollect (i.State s) Id Id] : Array γ :=
  Internal.iter s |>.toArray

@[always_inline, inline]
def toList {shape} {α : Type u} {β : Type v} {γ : Type w} [Sliceable shape α β γ]
    [i : SliceIter shape α] (s : Slice shape α) [Iterator (i.State s) Id γ]
    [Finite (i.State s) Id] [IteratorCollect (i.State s) Id Id] : List γ :=
  Internal.iter s |>.toList

@[always_inline, inline]
def toListRev {shape} {α : Type u} {β : Type v} {γ : Type w} [Sliceable shape α β γ]
    [i : SliceIter shape α] (s : Slice shape α) [Iterator (i.State s) Id γ]
    [Finite (i.State s) Id] : List γ :=
  Internal.iter s |>.toListRev

end Std.Slice
