/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init.Data.Queue
public import Std.Sync.Mutex
public import Std.Internal.Async.Select

public section

/-!
This module contains the implementation of `Std.Notify`. `Std.Notify` provides a lightweight
notification primitive for signaling between tasks or threads. It supports both synchronous
and asynchronous waiting, and is useful for cases where you want to notify one or more waiters
that an event has occurred.

Unlike a channel, `Std.Notify` does not buffer messages or carry data. It's simply a trigger.
If no one is waiting, notifications are lost. If one or more waiters are present, exactly one
will be woken up per notification.
-/

namespace Std
open Std.Internal.IO.Async

inductive Notify.Consumer (α : Type) where
  | normal (promise : IO.Promise α)
  | select (finished : Waiter α)

def Notify.Consumer.resolve (c : Consumer α) (x : α) : BaseIO Bool := do
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

/--
The central state structure for a `Notify`.
-/
structure Notify.State where

  /--
  Consumers that are blocked waiting for a notification.
  --/
  consumers : Std.Queue (Notify.Consumer Unit)

/--
A notify is a synchronization primitive that allows multiple consumers to wait
until notify is called.
-/
structure Notify where
  state : Std.Mutex Notify.State

namespace Notify

/--
Create a new notify.
-/
def new : BaseIO Notify := do
  return { state := ← Std.Mutex.new { consumers := ∅ } }

/--
Notify all currently waiting consumers.
-/
def notify (x : Notify) : BaseIO Unit := do
  x.state.atomically do
    let mut st ← get

    let mut remainingConsumers := st.consumers
    st := { st with consumers := ∅ }

    while true do
      if let some (consumer, rest) := remainingConsumers.dequeue? then
        remainingConsumers := rest
        discard <| consumer.resolve ()
      else
        break

    set st

/--
Notify exactly one waiting consumer (if any). Returns true if a consumer
was notified, false if no consumers were waiting.
-/
def notifyOne (x : Notify) : BaseIO Bool := do
  x.state.atomically do
    let mut st ← get

    if let some (consumer, rest) := st.consumers.dequeue? then
      st := { st with consumers := rest }
      set st
      consumer.resolve ()
    else
      return false

/--
Wait to be notified. Returns a task that completes when notify is called.
Note: if notify was called before wait, this will wait for the next notify call.
-/
def wait (x : Notify) : IO (AsyncTask Unit) :=
  x.state.atomically do
    let promise ← IO.Promise.new
    modify fun st => { st with consumers := st.consumers.enqueue (.normal promise) }
    IO.bindTask promise.result? fun
      | some res => pure <| Task.pure (.ok res)
      | none => throw (IO.userError "notify dropped")

/--
Creates a selector that waits for notifications
-/
def selector (notify : Notify) : Selector Unit := {
  tryFn := do
    return none

  registerFn := fun waiter => do
    notify.state.atomically do
      modify fun st => { st with consumers := st.consumers.enqueue (.select waiter) }

  unregisterFn := do
    notify.state.atomically do
      let st ← get

      let consumers ← st.consumers.filterM fun
        | .normal _ => return true
        | .select waiter => return !(← waiter.checkFinished)

      set { st with consumers }
}

end Notify
end Std
