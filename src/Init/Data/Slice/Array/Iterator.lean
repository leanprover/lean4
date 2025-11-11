/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Slice.Array.Basic
import Init.Data.Iterators.Combinators.Attach
public import Init.Data.Iterators.Combinators.ULift
import all Init.Data.Range.Polymorphic.Basic
public import Init.Data.Range.Polymorphic.Iterators
public import Init.Data.Slice.Operations
import Init.Omega

public section

/-!
This module provides slice notation for array slices (a.k.a. `Subarray`) and implements an iterator
for those slices.
-/

open Std Slice PRange Iterators

variable {shape : RangeShape} {α : Type u}

instance {s : Subarray α} : ToIterator s Id α :=
  .of _
    (Rco.Internal.iter (s.internalRepresentation.start...<s.internalRepresentation.stop)
      |>.attachWith (· < s.internalRepresentation.array.size) ?h
      |>.uLift
      |>.map fun | .up i => s.internalRepresentation.array[i.1])
where finally
  case h =>
    simp only [Rco.Internal.isPlausibleIndirectOutput_iter_iff, Membership.mem, and_imp]
    intro out _ h
    have := s.internalRepresentation.stop_le_array_size
    omega

universe v w

@[no_expose] instance {s : Subarray α} : Iterator (ToIterator.State s Id) Id α := inferInstance
@[no_expose] instance {s : Subarray α} : Finite (ToIterator.State s Id) Id := inferInstance
@[no_expose] instance {s : Subarray α} : IteratorCollect (ToIterator.State s Id) Id Id := .defaultImplementation
@[no_expose] instance {s : Subarray α} : IteratorCollectPartial (ToIterator.State s Id) Id Id := .defaultImplementation
@[no_expose] instance {s : Subarray α} {m : Type v → Type w} [Monad m] :
    IteratorLoop (ToIterator.State s Id) Id m := .defaultImplementation
@[no_expose] instance {s : Subarray α} {m : Type v → Type w} [Monad m] :
    IteratorLoopPartial (ToIterator.State s Id) Id m := .defaultImplementation
@[no_expose] instance {s : Subarray α} :
    IteratorSize (ToIterator.State s Id) Id := inferInstance
@[no_expose] instance {s : Subarray α} :
    IteratorSizePartial (ToIterator.State s Id) Id := inferInstance

@[no_expose]
instance {α : Type u} {m : Type v → Type w} :
    ForIn m (Subarray α) α where
  forIn xs init f := forIn (Std.Slice.Internal.iter xs) init f

/-!
Without defining the following function `Subarray.foldlM`, it is still possible to call
`subarray.foldlM`, which would be elaborated to `Slice.foldlM (s := subarray)`. However, in order to
maximize backward compatibility and avoid confusion in the manual entry for `Subarray`, we
explicitly provide the wrapper function `Subarray.foldlM` for `Slice.foldlM`, providing a more
specific docstring.
-/

/--
Folds a monadic operation from left to right over the elements in a subarray.
An accumulator of type `β` is constructed by starting with `init` and monadically combining each
element of the subarray with the current accumulator value in turn. The monad in question may permit
early termination or repetition.
Examples:
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
@[inline]
def Subarray.foldlM {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (f : β → α → m β) (init : β) (as : Subarray α) : m β :=
  Slice.foldlM f (init := init) as

/--
Folds an operation from left to right over the elements in a subarray.
An accumulator of type `β` is constructed by starting with `init` and combining each
element of the subarray with the current accumulator value in turn.
Examples:
 * `#["red", "green", "blue"].toSubarray.foldl (· + ·.length) 0 = 12`
 * `#["red", "green", "blue"].toSubarray.popFront.foldl (· + ·.length) 0 = 9`
-/
@[inline]
def Subarray.foldl {α : Type u} {β : Type v} (f : β → α → β) (init : β) (as : Subarray α) : β :=
  Slice.foldl f (init := init) as

/--
The implementation of `ForIn.forIn` for `Subarray`, which allows it to be used with `for` loops in
`do`-notation.
-/
@[inline]
def Subarray.forIn {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (s : Subarray α) (b : β) (f : α → β → m (ForInStep β)) : m β :=
  ForIn.forIn s b f

namespace Array

/--
Allocates a new array that contains the contents of the subarray.
-/
@[coe]
def ofSubarray (s : Subarray α) : Array α :=
  Slice.toArray s

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

@[inherit_doc Array.ofSubarray]
def Subarray.toArray (s : Subarray α) : Array α :=
  Array.ofSubarray s
