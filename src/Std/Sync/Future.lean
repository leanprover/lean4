/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Sync.Mutex
public import Std.Internal.Async.IO

public section

/-!
This module contains the implementation of `Std.Future` that is a write-once container for a value of type `α`.
Once resolved with a value, it cannot be changed or resolved again. It's similar to an `IO.Promise` but it exists
in order to make `Seletor` work correctly.
-/

namespace Std

open Internal.IO.Async

private inductive Consumer (α : Type) where
  | normal (promise : IO.Promise α)
  | select (finished : Waiter α)

private def Consumer.resolve (c : Consumer α) (x : α) : BaseIO Bool := do
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
A `Future` is a write-once container for a value of type `α`. Once resolved with a value, it cannot be
changed or resolved again.
-/
structure Future (α : Type) where
  private mk ::
  private state : Mutex (Option α)
  private consumers : Mutex (Array (Consumer α))
  private nonEmpty : Nonempty α

namespace Future

/--
Create a new unresolved `Future`.
-/
def new [h : Nonempty α] : BaseIO (Future α) := do
  return {
    state := ← Mutex.new none
    consumers := ← Mutex.new #[]
    nonEmpty := h
  }

/--
Attempt to resolve the future with the given value. Returns `true` if the future was successfully resolved
(was not already resolved). Returns `false` if the future was already resolved. When resolved, all
waiting consumers will be notified.
-/
def resolve (p : Future α) (value : α) : BaseIO Bool := do
  let consumersToNotify ← p.state.atomically do
    let current ← get
    match current with
    | some _ =>
      return none
    | none =>
      set (some value)
      let cs ← p.consumers.atomically do
        let cs ← get
        MonadState.set #[]
        return some cs
      return cs

  match consumersToNotify with
  | none =>
    return false

  | some consumers =>
    if consumers.isEmpty then
      return true

    for consumer in consumers do
      discard <| consumer.resolve value

    return true

/--
Check if the future has been resolved.
-/
def isResolved (p : Future α) : BaseIO Bool := do
  p.state.atomically do
    return (← get).isSome

/--
Get the value if the future is resolved, otherwise return `none`.
-/
def tryGet (p : Future α) : BaseIO (Option α) := do
  p.state.atomically do
    return (← get)

/--
Wait for the future to be resolved and return its value. Returns a task that will complete once the
future is resolved.
-/
def get [Inhabited α] (p : Future α) : BaseIO (Task α) := do
  p.state.atomically do
    match ← MonadState.get with
    | some value =>
      return .pure value
    | none =>
      let promise ← IO.Promise.new
      p.consumers.atomically do
        modify (·.push (.normal promise))

      BaseIO.bindTask promise.result? fun res =>
        match res with
        | some res => pure (Task.pure res)
        | none => unreachable!

/--
Creates a `Selector` that resolves once the future is resolved.
-/
def selector (p : Future α) : Selector α where
  tryFn := p.tryGet

  registerFn waiter := do
    p.state.atomically do
      match ← MonadState.get with
      | some value =>
        let lose := return ()
        let win promise := promise.resolve (.ok value)
        waiter.race lose win
      | none =>
        p.consumers.atomically do
          modify (·.push (.select waiter))

  unregisterFn := do
    p.consumers.atomically do
      let cs ← MonadState.get
      let filtered ← cs.filterM fun
        | .normal .. => return true
        | .select waiter => return !(← waiter.checkFinished)
      set filtered

def ofPromise (promise : IO.Promise α) : BaseIO (Std.Future (Option α)) := do
  let stdFuture ← Std.Future.new
  BaseIO.chainTask promise.result? (fun x => discard <| stdFuture.resolve x)
  return stdFuture

end Future
end Std
