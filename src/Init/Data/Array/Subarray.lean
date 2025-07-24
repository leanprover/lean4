/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Init.GetElem
import Init.Data.Array.GetLit
public import Init.Data.Slice.Basic

public section

set_option linter.indexVariables true -- Enforce naming conventions for index variables.
set_option linter.missingDocs true

universe u v w

/--
Internal representation of `Subarray`, which is an abbreviation for `Slice SubarrayData`.
-/
structure Std.Slice.Internal.SubarrayData (α : Type u) where
  /-- The underlying array. -/
  array : Array α
  /-- The starting index of the region of interest (inclusive). -/
  start : Nat
  /-- The ending index of the region of interest (exclusive). -/
  stop : Nat
  /--
  The starting index is no later than the ending index.

  The ending index is exclusive. If the starting and ending indices are equal, then the subarray is
  empty.
  -/
  start_le_stop : start ≤ stop
  /-- The stopping index is no later than the end of the array.

  The ending index is exclusive. If it is equal to the size of the array, then the last element of
  the array is in the subarray.
  -/
  stop_le_array_size : stop ≤ array.size

open Std.Slice

/--
A region of some underlying array.

A subarray contains an array together with the start and end indices of a region of interest.
Subarrays can be used to avoid copying or allocating space, while being more convenient than
tracking the bounds by hand. The region of interest consists of every index that is both greater
than or equal to `start` and strictly less than `stop`.
-/
abbrev Subarray (α : Type u) := Std.Slice (Internal.SubarrayData α)

instance {α : Type u} : Self (Std.Slice (Internal.SubarrayData α)) (Subarray α) where

@[always_inline, inline, expose, inherit_doc Internal.SubarrayData.array]
def Subarray.array (xs : Subarray α) : Array α :=
  xs.internalRepresentation.array

@[always_inline, inline, expose, inherit_doc Internal.SubarrayData.start]
def Subarray.start (xs : Subarray α) : Nat :=
  xs.internalRepresentation.start

@[always_inline, inline, expose, inherit_doc Internal.SubarrayData.stop]
def Subarray.stop (xs : Subarray α) : Nat :=
  xs.internalRepresentation.stop

@[always_inline, inline, expose, inherit_doc Internal.SubarrayData.start_le_stop]
def Subarray.start_le_stop (xs : Subarray α) : xs.start ≤ xs.stop :=
  xs.internalRepresentation.start_le_stop

@[always_inline, inline, expose, inherit_doc Internal.SubarrayData.stop_le_array_size]
def Subarray.stop_le_array_size (xs : Subarray α) : xs.stop ≤ xs.array.size :=
  xs.internalRepresentation.stop_le_array_size

namespace Subarray

/--
Computes the size of the subarray.
-/
def size (s : Subarray α) : Nat :=
  s.stop - s.start

theorem size_le_array_size {s : Subarray α} : s.size ≤ s.array.size := by
  let ⟨{array, start, stop, start_le_stop, stop_le_array_size}⟩ := s
  simp only [size, ge_iff_le]
  apply Nat.le_trans (Nat.sub_le stop start)
  assumption

/--
Extracts an element from the subarray.

The index is relative to the start of the subarray, rather than the underlying array.
-/
def get (s : Subarray α) (i : Fin s.size) : α :=
  have : s.start + i.val < s.array.size := by
   apply Nat.lt_of_lt_of_le _ s.stop_le_array_size
   have := i.isLt
   simp only [size] at this
   rw [Nat.add_comm]
   exact Nat.add_lt_of_lt_sub this
  s.array[s.start + i.val]

instance : GetElem (Subarray α) Nat α fun xs i => i < xs.size where
  getElem xs i h := xs.get ⟨i, h⟩

/--
Extracts an element from the subarray, or returns a default value `v₀` when the index is out of
bounds.

The index is relative to the start and end of the subarray, rather than the underlying array.
-/
@[inline] def getD (s : Subarray α) (i : Nat) (v₀ : α) : α :=
  if h : i < s.size then s[i] else v₀

/--
Extracts an element from the subarray, or returns a default value when the index is out of bounds.

The index is relative to the start and end of the subarray, rather than the underlying array. The
default value is that provided by the `Inhabited α` instance.
-/
abbrev get! [Inhabited α] (s : Subarray α) (i : Nat) : α :=
  getD s i default

/--
Shrinks the subarray by incrementing its starting index if possible, returning it unchanged if not.

Examples:
 * `#[1,2,3].toSubarray.popFront.toArray = #[2, 3]`
 * `#[1,2,3].toSubarray.popFront.popFront.toArray = #[3]`
 * `#[1,2,3].toSubarray.popFront.popFront.popFront.toArray = #[]`
 * `#[1,2,3].toSubarray.popFront.popFront.popFront.popFront.toArray = #[]`
-/
def popFront (s : Subarray α) : Subarray α :=
  if h : s.start < s.stop then
    ⟨{ s.internalRepresentation with
        start := s.start + 1,
        start_le_stop := Nat.le_of_lt_succ (Nat.add_lt_add_right h 1) }⟩
  else
    s

/--
The empty subarray.

This empty subarray is backed by an empty array.
-/
protected def empty : Subarray α := ⟨{
    array := #[]
    start := 0
    stop := 0
    start_le_stop := Nat.le_refl 0
    stop_le_array_size := Nat.le_refl 0
  }⟩

instance : EmptyCollection (Subarray α) :=
  ⟨Subarray.empty⟩

instance : Inhabited (Subarray α) :=
  ⟨{}⟩

/-!
`ForIn`, `foldlM`, `foldl` and other operations are implemented in `Init.Data.Slice.Array.Iterator`
using the slice iterator.
-/

/--
Folds a monadic operation from right to left over the elements in a subarray.

An accumulator of type `β` is constructed by starting with `init` and monadically combining each
element of the subarray with the current accumulator value in turn, moving from the end to the
start. The monad in question may permit early termination or repetition.

Examples:
```lean example
#eval #["red", "green", "blue"].toSubarray.foldrM (init := "") fun x acc => do
  let l ← Option.guard (· ≠ 0) x.length
  return s!"{acc}({l}){x} "
```
```output
some "(4)blue (5)green (3)red "
```
```lean example
#eval #["red", "green", "blue"].toSubarray.foldrM (init := 0) fun x acc => do
  let l ← Option.guard (· ≠ 5) x.length
  return s!"{acc}({l}){x} "
```
```output
none
```
-/
@[inline]
def foldrM {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (f : α → β → m β) (init : β) (as : Subarray α) : m β :=
  as.array.foldrM f (init := init) (start := as.stop) (stop := as.start)

/--
Checks whether any of the elements in a subarray satisfy a monadic Boolean predicate.

The elements are tested starting at the lowest index and moving up. The search terminates as soon as
an element that satisfies the predicate is found.

Example:
```lean example
#eval #["red", "green", "blue", "orange"].toSubarray.popFront.anyM fun x => do
  IO.println x
  pure (x == "blue")
```
```output
green
blue
```
```output
true
```
-/
@[inline]
def anyM {α : Type u} {m : Type → Type w} [Monad m] (p : α → m Bool) (as : Subarray α) : m Bool :=
  as.array.anyM p (start := as.start) (stop := as.stop)

/--
Checks whether all of the elements in a subarray satisfy a monadic Boolean predicate.

The elements are tested starting at the lowest index and moving up. The search terminates as soon as
an element that does not satisfy the predicate is found.

Example:
```lean example
#eval #["red", "green", "blue", "orange"].toSubarray.popFront.allM fun x => do
  IO.println x
  pure (x.length == 5)
```
```output
green
blue
```
```output
false
```
-/
@[inline]
def allM {α : Type u} {m : Type → Type w} [Monad m] (p : α → m Bool) (as : Subarray α) : m Bool :=
  as.array.allM p (start := as.start) (stop := as.stop)

/--
Runs a monadic action on each element of a subarray.

The elements are processed starting at the lowest index and moving up.
-/
@[inline]
def forM {α : Type u} {m : Type v → Type w} [Monad m] (f : α → m PUnit) (as : Subarray α) : m PUnit :=
  as.array.forM f (start := as.start) (stop := as.stop)

/--
Runs a monadic action on each element of a subarray, in reverse order.

The elements are processed starting at the highest index and moving down.
-/
@[inline]
def forRevM {α : Type u} {m : Type v → Type w} [Monad m] (f : α → m PUnit) (as : Subarray α) : m PUnit :=
  as.array.forRevM f (start := as.stop) (stop := as.start)

/--
Folds an operation from right to left over the elements in a subarray.

An accumulator of type `β` is constructed by starting with `init` and combining each element of the
subarray with the current accumulator value in turn, moving from the end to the start.

Examples:
 * `#eval #["red", "green", "blue"].toSubarray.foldr (·.length + ·) 0 = 12`
 * `#["red", "green", "blue"].toSubarray.popFront.foldlr (·.length + ·) 0 = 9`
-/
@[inline]
def foldr {α : Type u} {β : Type v} (f : α → β → β) (init : β) (as : Subarray α) : β :=
  Id.run <| as.foldrM (pure <| f · ·) (init := init)

/--
Checks whether any of the elements in a subarray satisfy a Boolean predicate.

The elements are tested starting at the lowest index and moving up. The search terminates as soon as
an element that satisfies the predicate is found.
-/
@[inline]
def any {α : Type u} (p : α → Bool) (as : Subarray α) : Bool :=
  Id.run <| as.anyM (pure <| p ·)

/--
Checks whether all of the elements in a subarray satisfy a Boolean predicate.

The elements are tested starting at the lowest index and moving up. The search terminates as soon as
an element that does not satisfy the predicate is found.
-/
@[inline]
def all {α : Type u} (p : α → Bool) (as : Subarray α) : Bool :=
  Id.run <| as.allM (pure <| p ·)

/--
Applies a monadic function to each element in a subarray in reverse order, stopping at the first
element for which the function succeeds by returning a value other than `none`. The succeeding value
is returned, or `none` if there is no success.

Example:
```lean example
#eval #["red", "green", "blue"].toSubarray.findSomeRevM? fun x => do
  IO.println x
  return Option.guard (· = 5) x.length
```
```output
blue
green
```
```output
some 5
```
-/
@[inline]
def findSomeRevM? {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (as : Subarray α) (f : α → m (Option β)) : m (Option β) :=
  let rec @[specialize] find : (i : Nat) → i ≤ as.size → m (Option β)
    | 0,   _ => pure none
    | i+1, h => do
      have : i < as.size := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) h
      let r ← f as[i]
      match r with
      | some _ => pure r
      | none   =>
        have : i ≤ as.size := Nat.le_of_lt this
        find i this
  find as.size (Nat.le_refl _)

/--
Applies a monadic Boolean predicate to each element in a subarray in reverse order, stopping at the
first element that satisfies the predicate. The element that satisfies the predicate is returned, or
`none` if no element satisfies it.

Example:
```lean example
#eval #["red", "green", "blue"].toSubarray.findRevM? fun x => do
  IO.println x
  return (x.length = 5)
```
```output
blue
green
```
```output
some 5
```
-/
@[inline]
def findRevM? {α : Type} {m : Type → Type w} [Monad m] (as : Subarray α) (p : α → m Bool) : m (Option α) :=
  as.findSomeRevM? fun a => return if (← p a) then some a else none

/--
Tests each element in a subarray with a Boolean predicate in reverse order, stopping at the first
element that satisfies the predicate. The element that satisfies the predicate is returned, or
`none` if no element satisfies the predicate.

Examples:
 * `#["red", "green", "blue"].toSubarray.findRev? (·.length ≠ 4) = some "green"`
 * `#["red", "green", "blue"].toSubarray.findRev? (fun _ => true) = some "blue"`
 * `#["red", "green", "blue"].toSubarray 0 0 |>.findRev? (fun _ => true) = none`
-/
@[inline]
def findRev? {α : Type} (as : Subarray α) (p : α → Bool) : Option α :=
  Id.run <| as.findRevM? (pure <| p ·)

end Subarray

namespace Array
variable {α : Type u}

/--
Returns a subarray of an array, with the given bounds.

If `start` or `stop` are not valid bounds for a subarray, then they are clamped to array's size.
Additionally, the starting index is clamped to the ending index.
-/
def toSubarray (as : Array α) (start : Nat := 0) (stop : Nat := as.size) : Subarray α :=
  if h₂ : stop ≤ as.size then
    if h₁ : start ≤ stop then
      ⟨{ array := as, start := start, stop := stop,
         start_le_stop := h₁, stop_le_array_size := h₂ }⟩
    else
      ⟨{ array := as, start := stop, stop := stop,
         start_le_stop := Nat.le_refl _, stop_le_array_size := h₂ }⟩
  else
    if h₁ : start ≤ as.size then
      ⟨{ array := as,
         start := start,
         stop := as.size,
         start_le_stop := h₁,
         stop_le_array_size := Nat.le_refl _ }⟩
    else
      ⟨{ array := as,
         start := as.size,
         stop := as.size,
         start_le_stop := Nat.le_refl _,
         stop_le_array_size := Nat.le_refl _ }⟩

/-- A subarray with the provided bounds.-/
syntax:max term noWs "[" withoutPosition(term ":" term) "]" : term
/-- A subarray with the provided lower bound that extends to the rest of the array. -/
syntax:max term noWs "[" withoutPosition(term ":") "]" : term
/-- A subarray with the provided upper bound, starting at the index 0. -/
syntax:max term noWs "[" withoutPosition(":" term) "]" : term

macro_rules
  | `($a[$start : $stop]) => `(Array.toSubarray $a $start $stop)
  | `($a[ : $stop])       => `(Array.toSubarray $a 0 $stop)
  | `($a[$start : ])      => `(let a := $a; Array.toSubarray a $start a.size)

end Array
