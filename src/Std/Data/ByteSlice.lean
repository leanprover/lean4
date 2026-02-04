/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init.Data.ByteArray
public import Init.Data.Slice.Basic
public import Init.Data.Slice.Notation
public import Init.Data.Range.Polymorphic.Nat
import Init.Data.Int.Lemmas
import Init.Data.Int.Order
import Init.Omega

/-!
This module defines the `ByteSlice` structure. It's a modified version of the `SubArray` code,
with some functions specific to `ByteSlice`.
-/

public section

set_option linter.indexVariables true
set_option linter.missingDocs true

universe u v w

/--
Internal representation of `ByteSlice`, which is an abbreviation for `Slice ByteSliceData`.
-/
structure Std.Slice.Internal.ByteSliceData where
  private mk ::

  /--
  The underlying byte array.
  -/
  byteArray : ByteArray

  /--
  The starting index of the region of interest (inclusive).
  -/
  start : Nat

  /--
  The ending index of the region of interest (exclusive).
  -/
  stop : Nat

  /--
  The starting index is no later than the ending index.

  The ending index is exclusive. If the starting and ending indices are equal, then the byte slice is
  empty.
  -/
  start_le_stop : start ≤ stop

  /-- The stopping index is no later than the end of the byte array.

  The ending index is exclusive. If it is equal to the size of the byte array, then the last byte of
  the byte array is in the byte slice.
  -/
  stop_le_size_byteArray : stop ≤ byteArray.size

open Std.Slice

/--
A region of some underlying byte array.

A byte slice contains a byte array together with the start and end indices of a region of interest.
Byte slices can be used to avoid copying or allocating space, while being more convenient than
tracking the bounds by hand. The region of interest consists of every index that is both greater
than or equal to `start` and strictly less than `stop`.
-/
abbrev ByteSlice := Std.Slice Internal.ByteSliceData

instance : Self (Std.Slice Internal.ByteSliceData) ByteSlice where

namespace ByteSlice

@[always_inline, inline, expose, inherit_doc Internal.ByteSliceData.byteArray]
def byteArray (xs : @& ByteSlice) : ByteArray :=
  xs.internalRepresentation.byteArray

@[always_inline, inline, expose, inherit_doc Internal.ByteSliceData.start]
def start (xs : @& ByteSlice) : Nat :=
  xs.internalRepresentation.start

@[always_inline, inline, expose, inherit_doc Internal.ByteSliceData.stop]
def stop (xs : @& ByteSlice) : Nat :=
  xs.internalRepresentation.stop

@[inherit_doc Internal.ByteSliceData.start_le_stop]
theorem start_le_stop (xs : ByteSlice) : xs.start ≤ xs.stop :=
  xs.internalRepresentation.start_le_stop

@[inherit_doc Internal.ByteSliceData.stop_le_size_byteArray]
theorem stop_le_size_byteArray (xs : ByteSlice) : xs.stop ≤ xs.byteArray.size :=
  xs.internalRepresentation.stop_le_size_byteArray

/--
Computes the size of the byte slice.
-/
def size (s : ByteSlice) : Nat :=
  s.stop - s.start

theorem size_le_size_byteArray {s : ByteSlice} : s.size ≤ s.byteArray.size := by
  let ⟨{byteArray, start, stop, start_le_stop, stop_le_size_byteArray}⟩ := s
  simp only [size, ge_iff_le]
  apply Nat.le_trans (Nat.sub_le stop start)
  assumption

/--
Extracts a byte from the byte slice.

The index is relative to the start of the byte slice, rather than the underlying byte array.
-/
def get (s : ByteSlice) (i : Fin s.size) : UInt8 :=
  have : s.start + i.val < s.byteArray.size := by
   apply Nat.lt_of_lt_of_le _ s.stop_le_size_byteArray
   have := i.isLt
   simp only [size] at this
   rw [Nat.add_comm]
   exact Nat.add_lt_of_lt_sub this
  s.byteArray[s.start + i.val]

instance : GetElem ByteSlice Nat UInt8 fun xs i => i < xs.size where
  getElem xs i h := xs.get ⟨i, h⟩

/--
Extracts a byte from the byte slice, or returns a default value `v₀` when the index is out of
bounds.

The index is relative to the start and end of the byte slice, rather than the underlying byte array.
-/
@[inline] def getD (s : ByteSlice) (i : Nat) (v₀ : UInt8) : UInt8 :=
  if h : i < s.size then s[i] else v₀

/--
Extracts a byte from the byte slice, or returns a default value when the index is out of bounds.

The index is relative to the start and end of the byte slice, rather than the underlying byte array. The
default value is 0.
-/
abbrev get! (s : ByteSlice) (i : Nat) : UInt8 :=
  getD s i 0

/--
The empty byte slice.

This empty byte slice is backed by an empty byte array.
-/
protected def empty : ByteSlice := ⟨{
    byteArray := ByteArray.mk #[]
    start := 0
    stop := 0
    start_le_stop := Nat.le_refl 0
    stop_le_size_byteArray := Nat.le_refl 0
  }⟩

/--
Creates a new ByteSlice of a ByteArray
-/
protected def ofByteArray (ba : ByteArray) : ByteSlice := ⟨{
    byteArray := ba
    start := 0
    stop := ba.size
    start_le_stop := Nat.zero_le _
    stop_le_size_byteArray := Nat.le_refl _
  }⟩

instance : EmptyCollection (ByteSlice) :=
  ⟨ByteSlice.empty⟩

instance : Inhabited (ByteSlice) :=
  ⟨{}⟩

/--
Converts a byte slice back to a byte array by copying the relevant portion.
-/
def toByteArray (s : ByteSlice) : ByteArray :=
  s.byteArray.extract s.start (s.start + s.size)

/--
Comparison function
-/
@[extern "lean_byteslice_beq"]
protected def beq (a b : @& ByteSlice) : Bool :=
  a.toByteArray == b.toByteArray

instance : BEq ByteSlice := ⟨ByteSlice.beq⟩

/--
Folds a monadic operation from right to left over the bytes in a byte slice.

An accumulator of type `β` is constructed by starting with `init` and monadically combining each
byte of the byte slice with the current accumulator value in turn, moving from the end to the
start. The monad in question may permit early termination or repetition.

Examples:
```lean example
#eval (ByteArray.mk #[1, 2, 3]).toByteSlice.foldrM (init := 0) fun x acc =>
  some x.toNat + acc
```
```output
some 6
```
-/
@[inline]
def foldrM {β : Type v} {m : Type v → Type w} [Monad m] (f : UInt8 → β → m β) (init : β) (as : ByteSlice) : m β :=
  let rec loop (i : Nat) (acc : β) : m β :=
    if h : i < as.size then do
      let newAcc ← f as[as.size - 1 - i] acc
      loop (i + 1) newAcc
    else
      pure acc
  loop 0 init

/--
Runs a monadic action on each byte of a byte slice.

The bytes are processed starting at the lowest index and moving up.
-/
@[inline]
def forM {m : Type v → Type w} [Monad m] (f : UInt8 → m PUnit) (as : ByteSlice) : m PUnit :=
  let rec loop (i : Nat) : m PUnit :=
    if h : i < as.size then do
      f as[i]
      loop (i + 1)
    else
      pure ⟨⟩
  loop 0

/--
Folds an operation from right to left over the bytes in a byte slice.

An accumulator of type `β` is constructed by starting with `init` and combining each byte of the
byte slice with the current accumulator value in turn, moving from the end to the start.

Examples:
 * `(ByteArray.mk #[1, 2, 3]).toByteSlice.foldr (·.toNat + ·) 0 = 6`
 * `(ByteArray.mk #[1, 2, 3]).toByteSlice.popFront.foldr (·.toNat + ·) 0 = 5`
-/
@[inline]
def foldr {β : Type v} (f : UInt8 → β → β) (init : β) (as : ByteSlice) : β :=
  Id.run <| as.foldrM (pure <| f · ·) (init := init)

/--
Creates a sub-slice of the byte slice with the given bounds.

If `start` or `stop` are not valid bounds for a sub-slice, then they are clamped to the slice's size.
Additionally, the starting index is clamped to the ending index.

The indices are relative to the current slice, not the underlying byte array.
-/
def slice (s : ByteSlice) (start : Nat := 0) (stop : Nat := s.size) : ByteSlice :=
  let actualStart := s.start + min start s.size
  let actualStop := s.start + min stop s.size
  if h₂ : actualStop ≤ s.byteArray.size then
    if h₁ : actualStart ≤ actualStop then
      ⟨{ byteArray := s.byteArray,
         start := actualStart,
         stop := actualStop,
         start_le_stop := h₁,
         stop_le_size_byteArray := h₂ }⟩
    else
      ⟨{ byteArray := s.byteArray,
         start := actualStop,
         stop := actualStop,
         start_le_stop := Nat.le_refl _,
         stop_le_size_byteArray := h₂ }⟩
  else
    ⟨{ byteArray := s.byteArray,
       start := s.start,
       stop := s.start,
       start_le_stop := Nat.le_refl _,
       stop_le_size_byteArray := Nat.le_trans (Nat.le_refl _) (Nat.le_trans s.start_le_stop s.stop_le_size_byteArray) }⟩

/--
Checks if the byte slice contains a specific byte value.

Returns `true` if any byte in the slice equals the given value, `false` otherwise.
-/
def contains (s : ByteSlice) (byte : UInt8) : Bool :=
  let rec loop (i : Nat) : Bool :=
    if h : i < s.size then
      if s[i] == byte then true
      else loop (i + 1)
    else
      false
  loop 0

end ByteSlice

namespace ByteArray

/--
Returns a byte slice of a byte array, with the given bounds.

If `start` or `stop` are not valid bounds for a byte slice, then they are clamped to byte array's size.
Additionally, the starting index is clamped to the ending index.
-/
def toByteSlice (as : ByteArray) (start : Nat := 0) (stop : Nat := as.size) : ByteSlice :=
  if h₂ : stop ≤ as.size then
    if h₁ : start ≤ stop then
      ⟨{ byteArray := as, start := start, stop := stop,
         start_le_stop := h₁, stop_le_size_byteArray := h₂ }⟩
    else
      ⟨{ byteArray := as, start := stop, stop := stop,
         start_le_stop := Nat.le_refl _, stop_le_size_byteArray := h₂ }⟩
  else
    if h₁ : start ≤ as.size then
      ⟨{ byteArray := as,
         start := start,
         stop := as.size,
         start_le_stop := h₁,
         stop_le_size_byteArray := Nat.le_refl _ }⟩
    else
      ⟨{ byteArray := as,
         start := as.size,
         stop := as.size,
         start_le_stop := Nat.le_refl _,
         stop_le_size_byteArray := Nat.le_refl _ }⟩

end ByteArray

open Std Slice PRange

variable {α : Type u}

section ByteArray

instance : Rcc.Sliceable ByteArray Nat ByteSlice where
  mkSlice xs range :=
    let halfOpenRange := Rcc.HasRcoIntersection.intersection range 0...<xs.size
    (xs.toByteSlice halfOpenRange.lower halfOpenRange.upper)

instance : Rco.Sliceable ByteArray Nat ByteSlice where
  mkSlice xs range :=
    let halfOpenRange := Rco.HasRcoIntersection.intersection range 0...<xs.size
    (xs.toByteSlice halfOpenRange.lower halfOpenRange.upper)

instance : Rci.Sliceable ByteArray Nat ByteSlice where
  mkSlice xs range :=
    let halfOpenRange := Rci.HasRcoIntersection.intersection range 0...<xs.size
    (xs.toByteSlice halfOpenRange.lower halfOpenRange.upper)

instance : Roc.Sliceable ByteArray Nat ByteSlice where
  mkSlice xs range :=
    let halfOpenRange := Roc.HasRcoIntersection.intersection range 0...<xs.size
    (xs.toByteSlice halfOpenRange.lower halfOpenRange.upper)

instance : Roo.Sliceable ByteArray Nat ByteSlice where
  mkSlice xs range :=
    let halfOpenRange := Roo.HasRcoIntersection.intersection range 0...<xs.size
    (xs.toByteSlice halfOpenRange.lower halfOpenRange.upper)

instance : Roi.Sliceable ByteArray Nat ByteSlice where
  mkSlice xs range :=
    let halfOpenRange := Roi.HasRcoIntersection.intersection range 0...<xs.size
    (xs.toByteSlice halfOpenRange.lower halfOpenRange.upper)

instance : Ric.Sliceable ByteArray Nat ByteSlice where
  mkSlice xs range :=
    let halfOpenRange := Ric.HasRcoIntersection.intersection range 0...<xs.size
    (xs.toByteSlice halfOpenRange.lower halfOpenRange.upper)

instance : Rio.Sliceable ByteArray Nat ByteSlice where
  mkSlice xs range :=
    let halfOpenRange := Rio.HasRcoIntersection.intersection range 0...<xs.size
    (xs.toByteSlice halfOpenRange.lower halfOpenRange.upper)

instance : Rii.Sliceable ByteArray Nat ByteSlice where
  mkSlice xs _ :=
    let halfOpenRange := 0...<xs.size
    (xs.toByteSlice halfOpenRange.lower halfOpenRange.upper)

end ByteArray

section ByteSlice

instance : Rcc.Sliceable ByteSlice Nat ByteSlice where
  mkSlice xs range :=
    let halfOpenRange := Rcc.HasRcoIntersection.intersection range 0...<xs.size
    (xs.slice halfOpenRange.lower halfOpenRange.upper)

instance : Rco.Sliceable ByteSlice Nat ByteSlice where
  mkSlice xs range :=
    let halfOpenRange := Rco.HasRcoIntersection.intersection range 0...<xs.size
    (xs.slice halfOpenRange.lower halfOpenRange.upper)

instance : Rci.Sliceable ByteSlice Nat ByteSlice where
  mkSlice xs range :=
    let halfOpenRange := Rci.HasRcoIntersection.intersection range 0...<xs.size
    (xs.slice halfOpenRange.lower halfOpenRange.upper)

instance : Roc.Sliceable ByteSlice Nat ByteSlice where
  mkSlice xs range :=
    let halfOpenRange := Roc.HasRcoIntersection.intersection range 0...<xs.size
    (xs.slice halfOpenRange.lower halfOpenRange.upper)

instance : Roo.Sliceable ByteSlice Nat ByteSlice where
  mkSlice xs range :=
    let halfOpenRange := Roo.HasRcoIntersection.intersection range 0...<xs.size
    (xs.slice halfOpenRange.lower halfOpenRange.upper)

instance : Roi.Sliceable ByteSlice Nat ByteSlice where
  mkSlice xs range :=
    let halfOpenRange := Roi.HasRcoIntersection.intersection range 0...<xs.size
    (xs.slice halfOpenRange.lower halfOpenRange.upper)

instance : Ric.Sliceable ByteSlice Nat ByteSlice where
  mkSlice xs range :=
    let halfOpenRange := Ric.HasRcoIntersection.intersection range 0...<xs.size
    (xs.slice halfOpenRange.lower halfOpenRange.upper)

instance : Rio.Sliceable ByteSlice Nat ByteSlice where
  mkSlice xs range :=
    let halfOpenRange := Rio.HasRcoIntersection.intersection range 0...<xs.size
    (xs.slice halfOpenRange.lower halfOpenRange.upper)

instance : Rii.Sliceable ByteSlice Nat ByteSlice where
  mkSlice xs _ :=
    let halfOpenRange := 0...<xs.size
    (xs.slice halfOpenRange.lower halfOpenRange.upper)

end ByteSlice
