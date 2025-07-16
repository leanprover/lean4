/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
module

prelude
public import Init.Data.Array.Basic
public import Init.Data.Array.DecidableEq
public import Init.Data.UInt.Basic
public import all Init.Data.UInt.BasicAux
public import Init.Data.Option.Basic
public import Init.Data.ByteArray
public import Init.Data.Iterators.Basic
public import Init.Data.Slice.Basic

public section

/--
A slice of bytes.
-/
structure ByteSlice where
  data : ByteArray
  start : Nat
  «end» : Nat
  valid : start ≤ «end» ∧ «end» ≤ data.size

namespace ByteSlice

/--
Creates a new `ByteSlice` from a `ByteArray.Iterator`.
-/
@[inline]
def ofIterator (data : ByteArray.Iterator) (size : Nat) (h : data.pos + size ≤ data.array.size) : ByteSlice :=
  { data := data.array, start := data.pos, «end» := data.pos + size, valid := And.intro (by simp) h }

/--
Creates a new `ByteSlice` from a `ByteArray`.
-/
@[inline]
def ofByteArray (data : ByteArray) : ByteSlice :=
  { data, start := 0, «end» := data.size, valid := by simp }

/--
Creates an empty `ByteSlice`.
-/
@[inline]
def empty : ByteSlice :=
  { data := ByteArray.empty, start := 0, «end» := 0, valid := by simp }

/--
Gets the size of the slice.
-/
@[inline]
def size (slice : ByteSlice) : Nat :=
  slice.«end» - slice.start

/--
Checks if the slice is empty.
-/
@[inline]
def isEmpty (slice : ByteSlice) : Bool :=
  slice.size = 0

/--
Gets a byte at the given index within the slice.
Returns `none` if the index is out of bounds.
-/
@[inline]
def get (slice : ByteSlice) (i : Nat) (h : i < slice.size := by get_elem_tactic) : UInt8 :=
  have h_bounds : slice.start + i < slice.data.size := by
    simp [size] at h
    have h1 := slice.valid.left
    have h2 := slice.valid.right
    have h3 : slice.start + i < slice.«end» := by
      rw [← Nat.add_sub_cancel' h1]
      exact Nat.add_lt_add_left h slice.start
    exact Nat.lt_of_lt_of_le h3 h2

  slice.data.get (slice.start + i) h_bounds

/--
Gets a byte at the given index within the slice.
Panics if the index is out of bounds.
-/
def get! (slice : ByteSlice) (i : Nat)  : UInt8 :=
  if h :i < slice.size then
    slice.get i
  else
    panic! "ByteSlice index out of bounds"

/--
Gets a byte at the given index within the slice.
Panics if the index is out of bounds.
-/
def get? (slice : ByteSlice) (i : Nat) : Option UInt8 :=
  if h : i < slice.size then
    some (slice.get i)
  else
    none

/--
Gets a byte at the given index within the slice.
Panics if the index is out of bounds.
-/
@[inline]
def getD (slice : ByteSlice) (i : Nat) (default : UInt8) : UInt8 :=
  slice.get? i |>.getD default

/--
Gets the first byte of the slice.
Returns `none` if the slice is empty.
-/
@[inline]
def first? (slice : ByteSlice) : Option UInt8 :=
  slice.get? 0

/--
Gets the first byte of the slice.
Returns `none` if the slice is empty.
-/
@[inline]
def nextSlice? (slice : ByteSlice) : Option ByteSlice :=
  if h : slice.end + 1 ≤ slice.data.size then
    some { slice with «end» := slice.end + 1, valid := And.intro (Nat.le_trans slice.valid.left (by simp)) h }
  else
    none

/--
Gets the last byte of the slice.
Returns `none` if the slice is empty.
-/
@[inline]
def last? (slice : ByteSlice) : Option UInt8 :=
  if slice.isEmpty then none else slice.get? (slice.size - 1)

/--
Creates a sub-slice from the given start index to the end.
Returns `none` if the start index is out of bounds.
-/
@[inline]
def drop (slice : ByteSlice) (n : Nat) : ByteSlice :=
  if h : n <= slice.size then
    let valid := by
      simp [size] at h;
      simp [slice.valid]
      have h := Nat.add_le_add_left (n := n) h slice.start
      rw [Nat.add_sub_cancel' slice.valid.left] at h
      exact h
    { slice with start := slice.start + n, valid }
  else
    { slice with start := slice.end, valid := by simp [slice.valid] }

/--
Creates a sub-slice with the first `n` elements.
Returns `none` if `n` is greater than the slice size.
-/
@[inline]
def take (slice : ByteSlice) (n : Nat) : ByteSlice :=
  if h : n <= slice.size then
    let newEnd := slice.start + n
    let valid := by
      constructor
      · simp [newEnd]
      · simp [newEnd]
        simp [size] at h
        have h3 : slice.start + n ≤ slice.start + (slice.«end» - slice.start) :=
          Nat.add_le_add_left h slice.start
        rw [Nat.add_sub_cancel' slice.valid.left] at h3
        exact Nat.le_trans h3 slice.valid.right
    { slice with «end» := newEnd, valid }
  else
    slice

/--
Creates a sub-slice from start index to end index (exclusive).
Returns the slice unchanged if indices are out of bounds.
-/
@[inline]
def slice (slice : ByteSlice) (start : Nat) (endIdx : Nat) : ByteSlice :=
  if h1 : start <= endIdx ∧ endIdx <= slice.size then
    let newStart := slice.start + start
    let newEnd := slice.start + endIdx

    let valid := by
      constructor
      · simp [newStart, newEnd]
        exact h1.left
      · simp [newEnd]
        simp [size] at h1
        have h4 : slice.start + endIdx ≤ slice.start + (slice.«end» - slice.start) :=
          Nat.add_le_add_left h1.right slice.start
        rw [Nat.add_sub_cancel' slice.valid.left] at h4
        exact Nat.le_trans h4 slice.valid.right
    { data := slice.data, start := newStart, «end» := newEnd, valid }
  else
    slice

/--
Finds the first occurrence of a byte in the slice.
Returns the index relative to the slice start, or `none` if not found.
-/
def indexOf? (slice : ByteSlice) (byte : UInt8) : Option Nat :=
  let rec loop (i : Nat) : Option Nat :=
    if h : i < slice.size then
      if slice.get i h = byte then
        some i
      else
        loop (i + 1)
    else
      none
  loop 0

/--
Checks if the slice starts with another slice.
-/
def startsWith (slice : ByteSlice) (pref : ByteSlice) : Bool :=
  if pref.size > slice.size then
    false
  else
    let rec loop (i : Nat) : Bool :=
      if h : i < pref.size then
        if h2 : i < slice.size then
          if slice.get i = pref.get i then
            loop (i + 1)
          else
            false
        else
          false
      else
        true
    loop 0

/---
Checks if the slice contains a specific byte.
-/
@[inline]
def contains (slice : ByteSlice) (byte : UInt8) : Bool :=
  slice.indexOf? byte |>.isSome

/--
Converts the slice to a ByteArray by copying.
-/
@[inline]
def toByteArray (slice : ByteSlice) : ByteArray :=
  slice.data.extract slice.start slice.end

@[extern "lean_byteslice_beq"]
protected def beq (a b : ByteSlice) : Bool :=
  BEq.beq a.toByteArray b.toByteArray

instance : BEq ByteSlice where
  beq := ByteSlice.beq

instance : GetElem ByteSlice Nat UInt8 (fun slice i => i < slice.size) where
  getElem := fun slice i h => slice.get i h
