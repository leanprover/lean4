/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Core
public import Init.Data.Slice.Array.Basic
import Init.Data.Iterators.Combinators.Attach
import Init.Data.Iterators.Combinators.FilterMap
import Init.Data.Iterators.Combinators.ULift
public import Init.Data.Iterators.Consumers.Collect
public import Init.Data.Iterators.Consumers.Loop
public import all Init.Data.Range.Polymorphic.Basic
public import Init.Data.Range.Polymorphic.Nat
public import Init.Data.Range.Polymorphic.Iterators
public import Init.Data.Slice.Operations

public section

/-!
This module provides slice notation for array slices (a.k.a. `Subarray`) and implements an iterator
for those slices.
-/

open Std Slice PRange Iterators

variable {shape : RangeShape} {α : Type u}

@[no_expose]
instance {s : Subarray α} : ToIterator s Id α :=
  .of _
    (PRange.Internal.iter (s.internalRepresentation.start...<s.internalRepresentation.stop)
      |>.attachWith (· < s.internalRepresentation.array.size) ?h
      |>.uLift
      |>.map fun | .up i => s.internalRepresentation.array[i.1])
where finally
  case h =>
    simp only [Internal.isPlausibleIndirectOutput_iter_iff, Membership.mem,
      SupportsUpperBound.IsSatisfied, and_imp]
    intro out _ h
    have := s.internalRepresentation.stop_le_array_size
    omega

@[no_expose] instance {s : Subarray α} : Iterator (ToIterator.State s Id) Id α := inferInstance
@[no_expose] instance {s : Subarray α} : Finite (ToIterator.State s Id) Id := inferInstance
@[no_expose] instance {s : Subarray α} : IteratorCollect (ToIterator.State s Id) Id Id := inferInstance
@[no_expose] instance {s : Subarray α} : IteratorCollectPartial (ToIterator.State s Id) Id Id := inferInstance
@[no_expose] instance {s : Subarray α} : IteratorLoop (ToIterator.State s Id) Id Id := inferInstance
@[no_expose] instance {s : Subarray α} : IteratorLoopPartial (ToIterator.State s Id) Id Id := inferInstance
@[no_expose] instance {s : Subarray α} : IteratorSize (ToIterator.State s Id) Id := inferInstance
@[no_expose] instance {s : Subarray α} : IteratorSizePartial (ToIterator.State s Id) Id := inferInstance

namespace Array

/--
Allocates a new array that contains the contents of the subarray.
-/
@[coe]
def ofSubarray (s : Subarray α) : Array α := Id.run do
  let mut as := mkEmpty (s.stop - s.start)
  for a in s do
    as := as.push a
  return as

instance : Coe (Subarray α) (Array α) := ⟨ofSubarray⟩

instance : Append (Subarray α) where
  append x y :=
   let a := x.toArray ++ y.toArray
   a.toSubarray 0 a.size

/-- `Subarray` representation. -/
protected def Subarray.repr [Repr α] (s : Subarray α) : Std.Format :=
  repr s.toArray ++ ".toSubarray"

instance [Repr α] : Repr (Subarray α) where
  reprPrec s  _ := Subarray.repr s

instance [ToString α] : ToString (Subarray α) where
  toString s := toString s.toArray

end Array
