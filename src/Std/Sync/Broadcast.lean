/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Data
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

private structure Slot (α : Type) where
  value : α
  remaining : Mutex Nat

private structure Bounded.State (α : Type) where
  producers : Std.Queue (IO.Promise Bool)
  waiters : Std.Queue (Bounded.Consumer α)

  buffer : CircularBuffer.Mutable α

  receivers : Std.TreeSet Nat
  nextId : Nat

  closed : Bool

private structure Bounded (α : Type) where
  state : Mutex (Bounded.State α)

private structure Bounded.Receiver (α : Type) where
  state : Mutex (Bounded.State α)
  next : Nat

namespace Bounded

def subscribe (bounded : Bounded α) : IO (Receiver α) :=
  sorry

end Bounded
end CloseableBroadcast
