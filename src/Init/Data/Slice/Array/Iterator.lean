/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
import Init.Core
import Init.Data.Slice.Array.Basic
import Init.Data.Iterators.Combinators.Attach
import Init.Data.Iterators.Combinators.FilterMap
import all Init.Data.Range.Polymorphic.Basic
import Init.Data.Range.Polymorphic.Nat
import Init.Data.Range.Polymorphic.Iterators
import Init.Data.Slice.Operations

/-!
This module provides slice notation for array slices (a.k.a. `Subarray`) and implements an iterator
for those slices.
-/

open Std Slice PRange Iterators

variable {shape : RangeShape} {α : Type u}

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

namespace Array

/--
Allocates a new array that contains the contents of the subarray.
-/
@[coe]
def ofSubarray [∀ xs : Subarray α, ToIterator xs Id α] [∀ xs : Subarray α, ForIn Id (Iter (α := (ToIterator.State xs Id)) α) α]
    (s : Subarray α) : Array α := Id.run do
  let mut as := mkEmpty (s.stop - s.start)
  for a in s do
    as := as.push a
  return as

instance : Coe (Subarray α) (Array α) := ⟨ofSubarray⟩

instance: Append (Subarray α) where
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
