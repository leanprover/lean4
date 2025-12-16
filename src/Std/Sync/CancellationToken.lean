/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Data
public import Init.Data.Queue
public import Std.Sync.Mutex
public import Std.Internal.Async.Select

public section

/-!
This module contains the implementation of `Std.CancellationToken`. `Std.CancellationToken` provides a
cancellation primitive for signaling cancellation between tasks or threads. It supports both synchronous
and asynchronous waiting, and is useful for cases where you want to notify one or more waiters
that a cancellation has occurred.
-/

namespace Std
open Std.Internal.IO.Async

/--
Reasons for cancellation.
-/
inductive CancellationReason where
  /--
  Cancelled due to a deadline or timeout
  -/
  | deadline

  /--
  Cancelled due to shutdown
  -/
  | shutdown

  /--
  Explicitly cancelled
  -/
  | cancel

  /--
  Custom cancellation reason
  -/
  | custom (msg : String)
  deriving Repr, BEq

instance : ToString CancellationReason where
  toString
    | .deadline => "deadline"
    | .shutdown => "shutdown"
    | .cancel => "cancel"
    | .custom msg => s!"custom(\"{msg}\")"

inductive CancellationToken.Consumer where
  | normal (promise : IO.Promise Unit)
  | select (finished : Waiter Unit)

def CancellationToken.Consumer.resolve (c : Consumer) : BaseIO Bool := do
  match c with
  | .normal promise =>
    promise.resolve ()
    return true
  | .select waiter =>
    let lose := return false
    let win promise := do
      promise.resolve (.ok ())
      return true
    waiter.race lose win

/--
The central state structure for a `CancellationToken`.
-/
structure CancellationToken.State where
  /--
  The cancellation reason if cancelled, none otherwise.
  -/
  reason : Option CancellationReason

  /--
  Consumers that are blocked waiting for cancellation.
  --/
  consumers : Std.Queue (CancellationToken.Consumer)

/--
A cancellation token is a synchronization primitive that allows multiple consumers to wait
until cancellation is requested.
-/
structure CancellationToken where
  state : Std.Mutex CancellationToken.State

namespace CancellationToken

/--
Creates a new cancellation token.
-/
def new : BaseIO CancellationToken := do
  return { state := ← Std.Mutex.new { reason := none, consumers := ∅ } }

/--
Cancels the token with the given reason, notifying all currently waiting consumers.
Once cancelled, the token remains cancelled.
-/
def cancel (x : CancellationToken) (reason : CancellationReason := .cancel) : BaseIO Unit := do
  x.state.atomically do
    let mut st ← get

    if st.reason.isSome then
      return

    let mut remainingConsumers := st.consumers
    st := { reason := some reason, consumers := ∅ }

    while true do
      if let some (consumer, rest) := remainingConsumers.dequeue? then
        remainingConsumers := rest
        discard <| consumer.resolve
      else
        break

    set st

/--
Checks if the token is cancelled.
-/
def isCancelled (x : CancellationToken) : BaseIO Bool := do
  x.state.atomically do
    let st ← get
    return st.reason.isSome

/--
Gets the cancellation reason if the token is cancelled.
-/
def getCancellationReason (x : CancellationToken) : BaseIO (Option CancellationReason) := do
  x.state.atomically do
    let st ← get
    return st.reason

/--
Waits for cancellation. Returns a task that completes when cancelled.
-/
def wait (x : CancellationToken) : IO (AsyncTask Unit) :=
  x.state.atomically do
    let st ← get

    if st.reason.isSome then
      return Task.pure (.ok ())

    let promise ← IO.Promise.new

    modify fun st => { st with consumers := st.consumers.enqueue (.normal promise) }

    IO.bindTask promise.result? fun
      | some _ => pure <| Task.pure (.ok ())
      | none => throw (IO.userError "cancellation token dropped")

/--
Creates a selector that waits for cancellation.
-/
def selector (token : CancellationToken) : Selector Unit := {
  tryFn := do
    if ← token.isCancelled then
      return some ()
    else
      return none

  registerFn := fun waiter => do
    token.state.atomically do
      let st ← get

      if st.reason.isSome then
        discard <| waiter.race (return false) (fun promise => do
          promise.resolve (.ok ())
          return true)
      else
        modify fun st => { st with consumers := st.consumers.enqueue (.select waiter) }

  unregisterFn := do
    token.state.atomically do
      let st ← get

      let consumers ← st.consumers.filterM fun
        | .normal _ => return true
        | .select waiter => return !(← waiter.checkFinished)

      set { st with consumers }
}

end CancellationToken
end Std
