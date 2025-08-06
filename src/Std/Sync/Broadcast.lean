/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init.System.Promise
public import Init.Data.Queue
public import Std.Sync.Mutex
public import Std.Internal.Async.Select

public section

/-!
This module contains the implementation of `Std.Broadcast`. `Std.Broadcast` provides a
broadcasting primitive for sending values to multiple consumers. It maintains a queue of
values and supports both synchronous and asynchronous waiting.
-/

namespace Std
namespace CloseableBroadcast

inductive Error where
  | closed
  | alreadyClosed

instance : ToString Error where
  toString
    | .closed => "trying to send on an already closed channel"
    | .alreadyClosed => "trying to close an already closed broadcast channel"

instance : MonadLift (EIO Error) IO where
  monadLift x := EIO.toIO (.userError <| toString ·) x

-- ??

open Internal.IO.Async in

private inductive Bounded.Consumer (α : Type) where
  | normal (promise : IO.Promise (Option α))
  | select (finished : Waiter (Option α))

private def Bounded.Consumer.resolve (c : Consumer α) (x : Option α) : BaseIO Bool := do
  match c with
  | .normal promise =>
    promise.resolve x
    return true
  | .select waiter =>
    let lose := return false
    let win promise := do
      promise.resolve (.ok x)
      return true
    waiter.race lose win

-- ??

/--
COMMENT
-/
structure MutableCircularBuffer (α : Type) where
  /--
  COMMENT
  -/
  capacity : Nat

  /--
  COMMENT
  -/
  capProof : capacity > 0
  
  /--
  COMMENT
  -/
  storage : Vector (IO.Ref (Option α)) capacity
  
  /--
  COMMENT
  -/
  size : Nat
  
  /--
  COMMENT
  -/
  head : Fin capacity
  
  /--
  COMMENT
  -/
  tail : Fin capacity

namespace MutableCircularBuffer

/--
COMMENT
-/
def new (capacity : Nat) (h : capacity > 0 := by decide) : IO (MutableCircularBuffer α) := do
  let storage ← Vector.mapM (fun _ => IO.mkRef none) (Vector.replicate capacity ())

  return {
    capacity := capacity,
    capProof := h,
    storage := storage,
    size := 0,
    head := ⟨0, h⟩,
    tail := ⟨0, h⟩,
  }

/--
COMMENT
-/
def isEmpty (buf : MutableCircularBuffer α) : Bool :=
  buf.size = 0

/--
COMMENT
-/
def isFull (buf : MutableCircularBuffer α) : Bool :=
  buf.size ≥ buf.capacity

/--
COMMENT
-/
def currentSize (buf : MutableCircularBuffer α) : Nat :=
  buf.size

/--
Pushes a new value into the buffer.
-/
def push (buf : MutableCircularBuffer α) (value : α) (_h : ¬buf.isFull) : IO (MutableCircularBuffer α) := do
  let tailRef := buf.storage.get buf.tail
  tailRef.set (some value)

  let size := buf.size + 1
  let tail : Fin buf.capacity := @Fin.ofNat _ ⟨Nat.ne_zero_iff_zero_lt.mpr buf.capProof⟩ (buf.tail + 1)

  pure { buf with tail, size }

/--
COMMENT
-/
def pop [Inhabited α] (buf : MutableCircularBuffer α) (_h : ¬buf.isEmpty) : IO (α × MutableCircularBuffer α) := do
  let headRef := buf.storage.get buf.head
  let value ← headRef.get

  let size := buf.size - 1
  let head : Fin buf.capacity := @Fin.ofNat _ ⟨Nat.ne_zero_iff_zero_lt.mpr buf.capProof⟩ (buf.head + 1)

  pure (value.get!, { buf with head, size })

end MutableCircularBuffer

private structure Bounded.State (α : Type) where
  producers : Std.Queue (IO.Promise Bool)

  consumers : Std.Queue (Bounded.Consumer α)
  capacity : Nat
  buf : Vector (IO.Ref (Option α)) capacity
  bufCount : Nat
  sendIdx : Nat
  hsend : sendIdx < capacity
  recvIdx : Nat
  hrecv : recvIdx < capacity
  closed : Bool

end CloseableBroadcast
