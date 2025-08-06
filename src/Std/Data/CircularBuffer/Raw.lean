/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init.Data.Array
public import Init.Data.Nat

public section

/-!
# Circular Buffer - Raw Structure Definition

This file defines the core data structures for `Std.CircularBuffer.Raw`.

The circular buffer is implemented as a bounded FIFO queue using a fixed-size array
with head and tail pointers that wrap around when they reach the end of the array.
-/

set_option linter.missingDocs true
set_option autoImplicit false

universe u v w

variable {α : Type u} {β : Type v} {δ : Type w} {m : Type w → Type w} [Monad m]

namespace Std
namespace CircularBuffer

/--
Internal representation of a circular buffer using an array with head/tail pointers.
-/
structure Raw (α : Type u) where
  /--
  The maximum capcaity of the storage
  -/
  capacity : Nat

  /--
  Invariant: capacity is always greater than 0
  -/
  capacityH : capacity > 0

  /--
  The underlying array storage
  -/
  data : Vector (Option α) capacity

  /--
  Index of the first element (read)
  -/
  read : Fin capacity

  /--
  Index of the last element (write)
  -/
  write : Fin capacity

  /--
  The size of the Raw
  -/
  size : Nat
namespace Raw

/-- Creates an empty circular buffer with the specified capacity. -/
def emptyWithCapacity (capacity : Nat) (h : capacity > 0 := by decide) : Raw α :=
  {
    capacity
    capacityH := h
    data := Vector.replicate capacity none
    read := ⟨0, h⟩
    write := ⟨0, h⟩
    size := 0
  }

/-- Returns true if the buffer contains no elements. -/
def isEmpty (raw : Raw α) : Bool :=
  raw.size = 0

/-- Returns true if the buffer is at full capacity. -/
def isFull (raw : Raw α) : Bool :=
  raw.size ≥ raw.capacity

/--
Enqueues an element to the back of the circular buffer.
If the buffer is full, the oldest element (at front) is overwritten.
-/
def enqueue (raw : Raw α) (value : α) (_  : ¬raw.isFull) : Raw α :=
  let write := @Fin.ofNat raw.capacity ⟨Nat.ne_zero_of_lt raw.capacityH⟩ (raw.write.val + 1 % raw.capacity)
  let size := raw.size + 1
  { raw with write, size, data := raw.data.set raw.write.val (some value) raw.write.isLt }

/--
Dequeues an element from the front of the circular buffer.
Returns none if the buffer is empty.
-/
def dequeue (raw : Raw α) : (Option α × Raw α) :=
  if raw.isEmpty then
    (none, raw)
  else
    let read := @Fin.ofNat raw.capacity ⟨Nat.ne_zero_of_lt raw.capacityH⟩ (raw.read.val + 1 % raw.capacity)
    let size := raw.size - 1
    let data := raw.data.get raw.read
    (data, { raw with read, size, data := raw.data.set raw.read.val none raw.read.isLt })

/--
Peeks at the element at the front of the buffer without removing it.
Returns none if the buffer is empty.
-/
def front? (raw : Raw α) : Option α :=
  if raw.isEmpty then none else raw.data.get raw.read

/--
Convert the circular buffer to an array containing all elements in order.
The elements are returned in the order they would be popped (FIFO order).
-/
def toArray (raw : Raw α) : Array α :=
  let rec go (i : Nat) (acc : Array α) : Array α :=
    if i < raw.size then
      let pos := (raw.read.val + i) % raw.capacity
      let posLt : pos < raw.capacity := Nat.mod_lt _ raw.capacityH
      match raw.data.get ⟨pos, posLt⟩ with
      | some val => go (i + 1) (acc.push val)
      | none => go (i + 1) acc
    else
      acc
  go 0 #[]

/--
Convert the circular buffer to an list containing all elements in order.
The elements are returned in the order they would be popped (FIFO order).
-/
def toList (raw : Raw α) : List α :=
  let rec go (i : Nat) (acc : List α) : List α :=
    if i < raw.size then
      let pos := (raw.read.val + i) % raw.capacity
      let posLt : pos < raw.capacity := Nat.mod_lt _ raw.capacityH
      match raw.data.get ⟨pos, posLt⟩ with
      | some val => go (i + 1) (val :: acc)
      | none => go (i + 1) acc
    else
      acc
  go 0 [] |>.reverse

end Raw
end CircularBuffer
end Std
