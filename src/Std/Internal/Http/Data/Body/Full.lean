/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Sync
public import Std.Internal.Async
public import Std.Internal.Http.Data.Chunk
public import Std.Internal.Http.Data.Body.Length
public import Init.Data.ByteArray

public section

/-!
# Full

A `Full` represents a fully-buffered HTTP body that contains data which can be consumed exactly once.
It wraps a `ByteArray` in a `Mutex`-protected `Option`, tracking whether the data has already been
consumed.
-/

namespace Std.Http.Body
open Std Internal IO Async

set_option linter.all true

/--
Typeclass for types that can be converted to a `ByteArray`.
-/
class ToByteArray (α : Type) where

  /--
  Transforms into a `ByteArray`
  -/
  toByteArray : α → ByteArray

instance : ToByteArray ByteArray where
  toByteArray := id

instance : ToByteArray String where
  toByteArray := String.toUTF8

open Internal.IO.Async in

private structure Full.State where
  /--
  The stored data as ByteArray. `some` if not yet consumed, `none` if already consumed or empty.
  -/
  data : Option ByteArray

  /--
  Whether the body has been closed.
  -/
  closed : Bool

  /--
  Waiters registered via `recvSelector` waiting for data to become available.
  -/
  waiters : Std.Queue (Waiter (Option Chunk))
deriving Nonempty

/--
A fully-buffered body that stores data as a `ByteArray`. The data can be consumed exactly once
via `recv`. After consumption, subsequent `recv` calls return `none`.
-/
structure Full where
  private mk ::
  private state : Mutex Full.State
deriving Nonempty

namespace Full

/--
Creates a new `Full` body containing the given data converted to `ByteArray`.
-/
def ofData [ToByteArray β] (data : β) : Async Full := do
  return { state := ← Mutex.new { data := some (ToByteArray.toByteArray data), closed := false, waiters := ∅ } }

/--
Creates an empty `Full` body with no data.
-/
def empty : Async Full := do
  return { state := ← Mutex.new { data := none, closed := true, waiters := ∅ } }

/--
Non-blocking receive. Returns the stored `ByteArray` if available and not yet consumed,
or `none` if the body is empty or already consumed.
-/
def recv? (full : Full) : Async (Option ByteArray) := do
  full.state.atomically do
    let st ← get
    match st.data with
    | some data =>
      -- Resolve any pending waiters with none (data consumed by this call)
      for waiter in st.waiters.toArray do
        let lose := return ()
        let win promise := promise.resolve (.ok none)
        waiter.race lose win
      set { st with data := none, closed := true, waiters := ∅ }
      return some data
    | none =>
      return none

/--
Blocking receive. Since `Full` bodies are already fully buffered, this behaves the same as `recv?`.
Returns the stored `ByteArray` if available, or `none` if consumed or empty.
The amount parameter is ignored for fully-buffered bodies.
-/
def recv (full : Full) (_count : Option UInt64) : Async (Option ByteArray) :=
  full.recv?

/--
Sends data to the body, replacing any previously stored data.
-/
private partial def tryWakeWaiter [Monad m] [MonadLiftT (ST IO.RealWorld) m] [MonadLiftT BaseIO m]
    (data : ByteArray) : AtomicT State m Bool := do
  match (← get).waiters.dequeue? with
  | none => return false
  | some (waiter, waiters) =>
    modify fun st => { st with waiters }
    let lose := return false
    let win promise := do
      promise.resolve (.ok (some (Chunk.ofByteArray data)))
      return true
    let success ← waiter.race lose win
    if success then return true
    else tryWakeWaiter data

/--
Sends data to the body, replacing any previously stored data.
-/
def send (full : Full) (data : ByteArray) : Async Unit := do
  full.state.atomically do
    let success ← tryWakeWaiter data
    if !success then
      modify fun st => { st with data := some data, closed := false }

/--
Checks if the body is closed (consumed or empty).
-/
def isClosed (full : Full) : Async Bool := do
  full.state.atomically do
    return (← get).closed

/--
Returns the known size of the body if data is available.
-/
def size? (full : Full) : Async (Option Body.Length) := do
  full.state.atomically do
    let st ← get
    match st.data with
    | some data => return some (.fixed data.size)
    | none => return none

open Internal.IO.Async in

/--
Creates a `Selector` that resolves once the `Full` body has data available and provides that
data as a `Chunk`. Returns `none` when the body is closed.
-/
def recvSelector (full : Full) : Selector (Option Chunk) where
  tryFn := do
    full.state.atomically do
      let st ← get
      match st.data with
      | some data =>
        set { st with data := none, closed := true }
        return some (some (Chunk.ofByteArray data))
      | none =>
        if st.closed then return some none
        else return none

  registerFn waiter := do
    full.state.atomically do
      let st ← get
      match st.data with
      | some data =>
        let lose := return ()
        let win promise := do
          promise.resolve (.ok (some (Chunk.ofByteArray data)))
          set { (← get) with data := none, closed := true }
        waiter.race lose win
      | none =>
        if st.closed then
          let lose := return ()
          let win promise := promise.resolve (.ok none)
          waiter.race lose win
        else
          modify fun st => { st with waiters := st.waiters.enqueue waiter }

  unregisterFn := do
    full.state.atomically do
      let st ← get
      let waiters ← st.waiters.filterM fun waiter => return !(← waiter.checkFinished)
      set { st with waiters }

end Full

end Std.Http.Body
