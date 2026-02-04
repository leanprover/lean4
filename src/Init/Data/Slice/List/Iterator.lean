/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Slice.List.Basic
public import Init.Data.Iterators.Producers.List
public import Init.Data.Iterators.Combinators.Take
import all Init.Data.Range.Polymorphic.Basic
public import Init.Data.Range.Polymorphic.Iterators
public import Init.Data.Slice.Operations
import Init.Omega

public section

/-!
This module implements an iterator for list slices.
-/

open Std Slice PRange Iterators

variable {α : Type u}

@[inline, expose, instance_reducible]
def ListSlice.instToIterator :=
  ToIterator.of (γ := Slice (Internal.ListSliceData α)) _ (fun s => match s.internalRepresentation.stop with
      | some n => s.internalRepresentation.list.iter.take n
      | none => s.internalRepresentation.list.iter.toTake)
attribute [instance] ListSlice.instToIterator

universe v w

instance : SliceSize (Internal.ListSliceData α) where
  size s := (Internal.iter s).length

@[no_expose]
instance {α : Type u} {m : Type v → Type w} [Monad m] :
    ForIn m (ListSlice α) α where
  forIn xs init f := forIn (Internal.iter xs) init f

namespace List

instance : Append (ListSlice α) where
  append x y :=
   let a := x.toList ++ y.toList
   a.toSlice 0 a.length

/-- `ListSlice` representation. -/
protected def ListSlice.repr [Repr α] (s : ListSlice α) : Std.Format :=
  let xs := s.toList
  repr xs ++ ".toSlice 0 " ++ toString xs.length

instance [Repr α] : Repr (ListSlice α) where
  reprPrec s  _ := ListSlice.repr s

instance [ToString α] : ToString (ListSlice α) where
  toString s := toString s.toArray

end List
