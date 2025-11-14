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

variable {shape : RangeShape} {α : Type u}

instance {s : ListSlice α} : ToIterator s Id α :=
  .of _ (match s.internalRepresentation.stop with
      | some n => s.internalRepresentation.list.iter.take n
      | none => s.internalRepresentation.list.iter.toTake)

universe v w

@[no_expose] instance {s : ListSlice α} : Iterator (ToIterator.State s Id) Id α := inferInstance
@[no_expose] instance {s : ListSlice α} : Finite (ToIterator.State s Id) Id := inferInstance
@[no_expose] instance {s : ListSlice α} : IteratorCollect (ToIterator.State s Id) Id Id := inferInstance
@[no_expose] instance {s : ListSlice α} : IteratorCollectPartial (ToIterator.State s Id) Id Id := inferInstance
@[no_expose] instance {s : ListSlice α} {m : Type v → Type w} [Monad m] :
    IteratorLoop (ToIterator.State s Id) Id m := inferInstance
@[no_expose] instance {s : ListSlice α} {m : Type v → Type w} [Monad m] :
    IteratorLoopPartial (ToIterator.State s Id) Id m := inferInstance

instance : SliceSize (Internal.ListSliceData α) where
  size s := (Internal.iter s).count

@[no_expose]
instance {α : Type u} {m : Type v → Type w} :
    ForIn m (ListSlice α) α where
  forIn xs init f := forIn (Internal.iter xs) init f

namespace List

/-- Allocates a new list that contains the contents of the slice. -/
def ofSlice (s : ListSlice α) : List α :=
  s.toList

docs_to_verso ofSlice

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

@[inherit_doc List.ofSlice]
def ListSlice.toList (s : ListSlice α) : List α :=
  List.ofSlice s
