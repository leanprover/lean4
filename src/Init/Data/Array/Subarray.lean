/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Array.Basic

set_option linter.indexVariables true -- Enforce naming conventions for index variables.
set_option linter.missingDocs true

universe u v w

/--
A region of some underlying array.

A subarray contains an array together with the start and end indices of a region of interest.
Subarrays can be used to avoid copying or allocating space, while being more convenient than
tracking the bounds by hand. The region of interest consists of every index that is both greater
than or equal to `start` and strictly less than `stop`.
-/
structure Subarray (α : Type u) where
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

namespace Subarray

/--
Computes the size of the subarray.
-/
def size (s : Subarray α) : Nat :=
  s.stop - s.start

theorem size_le_array_size {s : Subarray α} : s.size ≤ s.array.size := by
  let {array, start, stop, start_le_stop, stop_le_array_size} := s
  simp [size]
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
   simp [size] at this
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
    { s with start := s.start + 1, start_le_stop := Nat.le_of_lt_succ (Nat.add_lt_add_right h 1) }
  else
    s

/--
The empty subarray.

This empty subarray is backed by an empty array.
-/
protected def empty : Subarray α where
  array := #[]
  start := 0
  stop := 0
  start_le_stop := Nat.le_refl 0
  stop_le_array_size := Nat.le_refl 0

instance : EmptyCollection (Subarray α) :=
  ⟨Subarray.empty⟩

instance : Inhabited (Subarray α) :=
  ⟨{}⟩

/--
The run-time implementation of `ForIn.forIn` for `Subarray`, which allows it to be used with `for`
loops in `do`-notation.

This definition replaces `Subarray.forIn`.
-/
@[inline] unsafe def forInUnsafe {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (s : Subarray α) (b : β) (f : α → β → m (ForInStep β)) : m β :=
  let sz := USize.ofNat s.stop
  let rec @[specialize] loop (i : USize) (b : β) : m β := do
    if i < sz then
      let a := s.array.uget i lcProof
      match (← f a b) with
      | ForInStep.done  b => pure b
      | ForInStep.yield b => loop (i+1) b
    else
      pure b
  loop (USize.ofNat s.start) b

/--
The implementation of `ForIn.forIn` for `Subarray`, which allows it to be used with `for` loops in
`do`-notation.
-/
-- TODO: provide reference implementation
@[implemented_by Subarray.forInUnsafe]
protected opaque forIn {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (s : Subarray α) (b : β) (f : α → β → m (ForInStep β)) : m β :=
  pure b

instance : ForIn m (Subarray α) α where
  forIn := Subarray.forIn

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
def foldlM {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (f : β → α → m β) (init : β) (as : Subarray α) : m β :=
  as.array.foldlM f (init := init) (start := as.start) (stop := as.stop)

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
Folds an operation from left to right over the elements in a subarray.

An accumulator of type `β` is constructed by starting with `init` and combining each
element of the subarray with the current accumulator value in turn.

Examples:
 * `#["red", "green", "blue"].toSubarray.foldl (· + ·.length) 0 = 12`
 * `#["red", "green", "blue"].toSubarray.popFront.foldl (· + ·.length) 0 = 9`
-/
@[inline]
def foldl {α : Type u} {β : Type v} (f : β → α → β) (init : β) (as : Subarray α) : β :=
  Id.run <| as.foldlM f (init := init)

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
  Id.run <| as.foldrM f (init := init)

/--
Checks whether any of the elements in a subarray satisfy a Boolean predicate.

The elements are tested starting at the lowest index and moving up. The search terminates as soon as
an element that satisfies the predicate is found.
-/
@[inline]
def any {α : Type u} (p : α → Bool) (as : Subarray α) : Bool :=
  Id.run <| as.anyM p

/--
Checks whether all of the elements in a subarray satisfy a Boolean predicate.

The elements are tested starting at the lowest index and moving up. The search terminates as soon as
an element that does not satisfy the predicate is found.
-/
@[inline]
def all {α : Type u} (p : α → Bool) (as : Subarray α) : Bool :=
  Id.run <| as.allM p

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
  Id.run <| as.findRevM? p

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
      { array := as, start := start, stop := stop,
        start_le_stop := h₁, stop_le_array_size := h₂ }
    else
      { array := as, start := stop, stop := stop,
        start_le_stop := Nat.le_refl _, stop_le_array_size := h₂ }
  else
    if h₁ : start ≤ as.size then
      { array := as,
        start := start,
        stop := as.size,
        start_le_stop := h₁,
        stop_le_array_size := Nat.le_refl _ }
    else
      { array := as,
        start := as.size,
        stop := as.size,
        start_le_stop := Nat.le_refl _,
        stop_le_array_size := Nat.le_refl _ }

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

@[inherit_doc Array.ofSubarray]
def Subarray.toArray (s : Subarray α) : Array α :=
  Array.ofSubarray s

instance : Append (Subarray α) where
  append x y :=
   let a := x.toArray ++ y.toArray
   a.toSubarray 0 a.size

instance [Repr α] : Repr (Subarray α) where
  reprPrec s  _ := repr s.toArray ++ ".toSubarray"

instance [ToString α] : ToString (Subarray α) where
  toString s := toString s.toArray
