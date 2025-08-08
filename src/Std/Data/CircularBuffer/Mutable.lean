module

prelude
public import Init.Data.Array
public import Init.Data.Nat
public import Init.System.IO

public section

/-!
# Mutable Circular Buffer - mutable Structure Definition

This file defines the core data structures for a mutable circular buffer.

The circular buffer is implemented as a bounded FIFO queue using a fixed-size array
of IO references with head and tail pointers that wrap around when they reach the end of the array.
-/

set_option linter.missingDocs true
set_option autoImplicit false

universe u v w

variable {α : Type} {β : Type v} {δ : Type w} {m : Type w → Type w} [Monad m]

namespace Std
namespace CircularBuffer

/--
Internal representation of a mutable circular buffer using an array of IO references with head/tail pointers.
-/
structure Mutable (α : Type) where
  /--
  The maximum capacity of the storage
  -/
  capacity : Nat

  /--
  Invariant: capacity is always greater than 0
  -/
  capacityH : capacity > 0

  /--
  The underlying array storage of IO references
  -/
  data : Vector (IO.Ref (Option α)) capacity

  /--
  Index of the first element (read)
  -/
  read : Fin capacity

  /--
  Index of the last element (write)
  -/
  write : Fin capacity

  /--
  The size of the Mutable
  -/
  size : Nat

namespace Mutable

/-- Creates an empty mutable circular buffer with the specified capacity. -/
def emptyWithCapacity (capacity : Nat) (h : capacity > 0 := by decide) : IO (Mutable α) := do
  let storage ← Vector.mapM (fun _ => IO.mkRef none) (Vector.replicate capacity ())

  return {
    capacity
    capacityH := h
    data := storage
    read := ⟨0, h⟩
    write := ⟨0, h⟩
    size := 0
  }

/-- Returns true if the buffer contains no elements. -/
def isEmpty (buf : Mutable α) : Bool :=
  buf.size = 0

/-- Returns true if the buffer is at full capacity. -/
def isFull (buf : Mutable α) : Bool :=
  buf.size ≥ buf.capacity

/--
Enqueues an element to the back of the circular buffer.
If the buffer is full, the oldest element (at front) is overwritten.
-/
def enqueue [Inhabited α] (mutable : Mutable α) (value : α) : IO (Mutable α) := do
  let tailRef := mutable.data.get mutable.write
  tailRef.set (some value)

  let size := mutable.size + 1
  let write : Fin mutable.capacity := @Fin.ofNat _ ⟨Nat.ne_zero_iff_zero_lt.mpr mutable.capacityH⟩ (mutable.write + 1)

  pure { mutable with write, size }

/--
Dequeues an element from the front of the circular buffer.
Returns none if the buffer is empty.
-/
def dequeue (mutable : Mutable α) : IO (Option α × Mutable α) := do
  let readRef := mutable.data.get mutable.read
  let value ← readRef.get

  let size := mutable.size - 1
  let read : Fin mutable.capacity := @Fin.ofNat _ ⟨Nat.ne_zero_iff_zero_lt.mpr mutable.capacityH⟩ (mutable.read + 1)

  pure (value, { mutable with read, size })

/--
Peeks at the element at the front of the buffer without removing it.
Returns none if the buffer is empty.
-/
def front? (mutable : Mutable α) : IO (Option α) := do
  if mutable.isEmpty then
    return none
  else
    let valueRef := mutable.data.get mutable.read
    valueRef.get

/--
Peeks at the element at the front of the buffer without removing it.
Returns none if the buffer is empty.
-/
def get? (mutable : Mutable α) (place : Nat) : IO (Option (IO.Ref (Option α))) := do
  if mutable.size ≥ place then
    return none
  else
    let idx := (@Fin.ofNat mutable.capacity ⟨Nat.ne_zero_of_lt mutable.capacityH⟩ (mutable.read.val + place))
    let valueRef := mutable.data.get idx
    return some valueRef

/--
Convert the mutable circular buffer to an array containing all elements in order.
The elements are returned in the order they would be popped (FIFO order).
-/
def toArray (mutable : Mutable α) : IO (Array α) := do
  let rec go (i : Nat) (acc : Array α) : IO (Array α) := do
    if i < mutable.size then
      let pos := (mutable.read.val + i) % mutable.capacity
      let posLt : pos < mutable.capacity := Nat.mod_lt _ mutable.capacityH
      let valueRef := mutable.data.get ⟨pos, posLt⟩
      let value ← valueRef.get
      match value with
      | some val => go (i + 1) (acc.push val)
      | none => go (i + 1) acc
    else
      return acc
  go 0 #[]


/--
Convert the mutable circular buffer to a list containing all elements in order.
The elements are returned in the order they would be popped (FIFO order).
-/
@[inline] def toList (mutable : Mutable α) : IO (List α) := do
  let arr ← mutable.toArray
  return arr.toList

/--
Get the current size of the buffer.
-/
@[inline] def getSize (mutable : Mutable α) : Nat :=
  mutable.size

/--
Get the capacity of the buffer.
-/
@[inline] def getCapacity (mutable : Mutable α) : Nat :=
  mutable.capacity

end Mutable
end CircularBuffer
end Std
