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

structure _root_.Std.Slice (γ : Type u) where
  internalRepresentation : γ

class Self (α : Type u) (β : outParam (Type u)) where
  eq : α = β := by rfl

/--
This typeclass signifies that the type `α` supports slice notation with index type `β`.
The slices contain elements of type `γ`.
-/
class Sliceable (shape : RangeShape) (α : Type u) (β : outParam (Type v))
    (γ : outParam (Type w)) where
  mkSlice (carrier : α) (range : PRange shape β) : γ

class ToIterator {γ : Type u} (x : γ) (m : Type w → Type w') (β : outParam (Type w)) where
  State : Type w
  iterMInternal : IterM (α := State) m β

@[always_inline, inline, expose]
def ToIterator.iterM (x : γ) [ToIterator x m β] : IterM (α := ToIterator.State x m) m β :=
  ToIterator.iterMInternal (x := x)

@[always_inline, inline, expose]
def ToIterator.iter (x : γ) [ToIterator x Id β] : Iter (α := ToIterator.State x Id) β :=
  ToIterator.iterM x |>.toIter

@[always_inline, inline, expose]
def ToIterator.ofM {x : γ} (State : Type w)
    (iterM : IterM (α := State) m β) :
    ToIterator x m β where
  State := State
  iterMInternal := iterM

@[always_inline, inline, expose]
def ToIterator.of {x : γ} (State : Type w)
    (iter : Iter (α := State) β) :
    ToIterator x Id β where
  State := State
  iterMInternal := iter.toIterM

instance {x : γ} {State : Type w} {iter}
    [Iterator State m β] :
    letI i : ToIterator x m β := .ofM State iter
    Iterator (α := i.State) m β :=
  inferInstanceAs <| Iterator State m β

instance {x : γ} {State : Type w} {iter}
    [Iterator (α := State) m β] [Finite State m] :
    letI i : ToIterator x m β := .ofM State iter
    Finite (α := i.State) m :=
  inferInstanceAs <| Finite (α := State) m

instance {x : γ} {State : Type w} {iter}
    [Iterator (α := State) m β] [IteratorCollect State m n] :
    letI i : ToIterator x m β := .ofM State iter
    IteratorCollect (α := i.State) m n :=
  inferInstanceAs <| IteratorCollect (α := State) m n

instance {x : γ} {State : Type w} {iter}
    [Iterator (α := State) m β] [IteratorCollectPartial State m n] :
    letI i : ToIterator x m β := .ofM State iter
    IteratorCollectPartial (α := i.State) m n :=
  inferInstanceAs <| IteratorCollectPartial (α := State) m n

instance {x : γ} {State : Type w} {iter}
    [Iterator (α := State) m β] [IteratorLoop State m n] :
    letI i : ToIterator x m β := .ofM State iter
    IteratorLoop (α := i.State) m n :=
  inferInstanceAs <| IteratorLoop (α := State) m n

instance {x : γ} {State : Type w} {iter}
    [Iterator (α := State) m β] [IteratorLoopPartial State m n] :
    letI i : ToIterator x m β := .ofM State iter
    IteratorLoopPartial (α := i.State) m n :=
  inferInstanceAs <| IteratorLoopPartial (α := State) m n

instance {x : γ} {State : Type w} {iter}
    [Iterator (α := State) m β] [IteratorSize State m] :
    letI i : ToIterator x m β := .ofM State iter
    IteratorSize (α := i.State) m :=
  inferInstanceAs <| IteratorSize (α := State) m

instance {x : γ} {State : Type w} {iter}
    [Iterator (α := State) m β] [IteratorSizePartial State m] :
    letI i : ToIterator x m β := .ofM State iter
    IteratorSizePartial (α := i.State) m :=
  inferInstanceAs <| IteratorSizePartial (α := State) m

instance {x : γ} [ToIterator x m β] : ToIterator (Slice.mk x) m β where
  State := ToIterator.State x m
  iterMInternal := ToIterator.iterMInternal

macro_rules
  | `($c[*...*]) => `(Sliceable.mkSlice $c *...*)
  | `($c[$a...*]) => `(Sliceable.mkSlice $c $a...*)
  | `($c[$a<...*]) => `(Sliceable.mkSlice $c $a...*)
  | `($c[*...<$b]) => `(Sliceable.mkSlice $c *...<$b)
  | `($c[$a...<$b]) => `(Sliceable.mkSlice $c $a...<$b)
  | `($c[$a<...<$b]) => `(Sliceable.mkSlice $c $a...<$b)
  | `($c[*...$b]) => `(Sliceable.mkSlice $c *...<$b)
  | `($c[$a...$b]) => `(Sliceable.mkSlice $c $a...<$b)
  | `($c[$a<...$b]) => `(Sliceable.mkSlice $c $a...<$b)
  | `($c[*...=$b]) => `(Sliceable.mkSlice $c *...=$b)
  | `($c[$a...=$b]) => `(Sliceable.mkSlice $c $a...=$b)
  | `($c[$a<...=$b]) => `(Sliceable.mkSlice $c $a...=$b)

/--
Internal function to obtain an iterator from a slice. Users should import `Std.Data.Iterators`
and use `Std.Slice.iter` instead.
-/
@[always_inline, inline]
def Internal.iter (s : Slice γ) [ToIterator s Id β] :=
  ToIterator.iter s

/--
Returns the number of elements -- not necessarily distinct -- in the given slice.
-/
@[always_inline, inline]
def size (s : Slice γ) [ToIterator s Id β] [Iterator (ToIterator.State s Id) Id β]
    [IteratorSize (ToIterator.State s Id) Id] :=
  Internal.iter s |>.size

@[always_inline, inline]
def toArray (s : Slice β) [ToIterator s Id β] [Iterator (ToIterator.State s Id) Id β]
    [IteratorCollect (ToIterator.State s Id) Id Id] [Finite (ToIterator.State s Id) Id] : Array β :=
  Internal.iter s |>.toArray

@[always_inline, inline]
def toList (s : Slice β) [ToIterator s Id β] [Iterator (ToIterator.State s Id) Id β]
    [IteratorCollect (ToIterator.State s Id) Id Id] [Finite (ToIterator.State s Id) Id] : List β :=
  Internal.iter s |>.toList

@[always_inline, inline]
def toListRev (s : Slice β) [ToIterator s Id β] [Iterator (ToIterator.State s Id) Id β]
    [IteratorCollect (ToIterator.State s Id) Id Id] [Finite (ToIterator.State s Id) Id] : List β :=
  Internal.iter s |>.toListRev

end Std.Slice
