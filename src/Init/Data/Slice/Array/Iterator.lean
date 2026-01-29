/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Slice.Array.Basic
public import Init.Data.Slice.Operations
import Init.Data.Iterators.Combinators.Attach
public import Init.Data.Iterators.Combinators.ULift
import all Init.Data.Range.Polymorphic.Basic
public import Init.Data.Range.Polymorphic.Iterators
public import Init.Data.Slice.Operations
import Init.Omega
import Init.Data.Iterators.Lemmas.Combinators.Monadic.FilterMap

public section

/-!
This module implements an iterator for array slices (`Subarray`).
-/

open Std Slice PRange Iterators

variable {shape : RangeShape} {α : Type u}

@[unbox]
structure SubarrayIterator (α : Type u) where
  xs : Subarray α

@[inline, expose]
def SubarrayIterator.step :
    IterM (α := SubarrayIterator α) Id α → IterStep (IterM (α := SubarrayIterator α) m α) α
  | ⟨⟨xs⟩⟩ =>
    if h : xs.start < xs.stop then
      have := xs.start_le_stop; have := xs.stop_le_array_size
      .yield ⟨⟨xs.array, xs.start + 1, xs.stop, by omega, xs.stop_le_array_size⟩⟩ xs.array[xs.start]
    else
      .done

instance : Iterator (SubarrayIterator α) Id α where
  IsPlausibleStep it step := step = SubarrayIterator.step it
  step it := pure <| .deflate ⟨SubarrayIterator.step it, rfl⟩

private def SubarrayIterator.instFinitelessRelation : FinitenessRelation (SubarrayIterator α) Id where
  Rel := InvImage WellFoundedRelation.rel (fun it => it.internalState.xs.stop - it.internalState.xs.start)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    simp [IterM.IsPlausibleSuccessorOf, IterM.IsPlausibleStep, Iterator.IsPlausibleStep, step] at h
    split at h
    · cases h
      simp only [InvImage, Subarray.stop, Subarray.start, WellFoundedRelation.rel, InvImage,
        Nat.lt_wfRel, sizeOf_nat]
      exact Nat.sub_succ_lt_self _ _ ‹_›
    · cases h

instance SubarrayIterator.instFinite : Finite (SubarrayIterator α) Id :=
  .of_finitenessRelation instFinitelessRelation

instance [Monad m] : IteratorLoop (SubarrayIterator α) Id m := .defaultImplementation

@[inline, expose]
def Subarray.instToIterator :=
  ToIterator.of (γ := Slice (Internal.SubarrayData α)) (β := α) (SubarrayIterator α) (⟨⟨·⟩⟩)
attribute [instance] Subarray.instToIterator

universe v w

instance : SliceSize (Internal.SubarrayData α) where
  size s := s.internalRepresentation.stop - s.internalRepresentation.start

instance {α : Type u} {m : Type v → Type w} [Monad m] : ForIn m (Subarray α) α :=
  inferInstance

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

/--
Allocates a new array that contains the contents of the subarray.
-/
@[coe]
def Subarray.toArray (s : Subarray α) : Array α :=
  Slice.toArray s

instance instCoeSubarrayArray : Coe (Subarray α) (Array α) :=
  ⟨Subarray.toArray⟩

@[inherit_doc Subarray.toArray]
def Subarray.copy (s : Subarray α) : Array α :=
  Slice.toArray s

@[simp]
theorem Subarray.copy_eq_toArray {s : Subarray α} :
    s.copy = s.toArray :=
  (rfl)

@[grind =]
theorem Subarray.sliceToArray_eq_toArray {s : Subarray α} :
    Slice.toArray s = s.toArray :=
  (rfl)

namespace Array

@[inherit_doc Subarray.toArray]
def ofSubarray (s : Subarray α) : Array α :=
  Slice.toArray s

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
