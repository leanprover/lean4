/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Data
public import Init.Data.Queue
public import Init.Data.Vector
public import Std.Sync.Mutex
public import Std.Internal.Async.IO

public section

namespace Std

open Std.Internal.Async.IO
open Std.Internal.IO.Async

/-!
The `Std.Sync.Broadcast` module implements a broadcasting primitive for sending values
to multiple consumers. It maintains a queue of values and supports both synchronous
and asynchronous waiting.

This module is heavily inspired by `Std.Sync.Channel` as well as
[tokio’s broadcast implementation](https://github.com/tokio-rs/tokio/blob/master/tokio/src/sync/broadcast.rs).
-/

/--
Errors that may be thrown while interacting with the broadcast channel API.
-/
inductive Broadcast.Error where
  /--
  Tried to send to a closed broadcast channel.
  -/
  | closed

  /--
  Tried to close an already closed broadcast channel.
  -/
  | alreadyClosed

  /--
  Tried to unsubscribe a channel that already is not part of it.
  -/
  | notSubscribed

deriving Repr, DecidableEq, Hashable

instance instToStringBroadcastError : ToString Broadcast.Error where
  toString
    | .closed => "attempted to send on an already closed channel"
    | .alreadyClosed => "attempted to close an already closed broadcast channel"
    | .notSubscribed => "receiver not subscribed in a broadcast channel"

instance instMonadLiftBroadcastIO : MonadLift (EIO Broadcast.Error) IO where
  monadLift x := EIO.toIO (.userError <| toString ·) x

private structure Broadcast.Consumer (α : Type) where
  promise : IO.Promise Bool
  waiter : Option (Internal.IO.Async.Waiter (Option α))

private def Broadcast.Consumer.resolve (c : Broadcast.Consumer α) (b : Bool) : BaseIO Unit :=
  c.promise.resolve b

private structure Slot (α : Type) where
  value : Option α
  pos : Nat
  remaining : Nat
deriving Inhabited, Repr

private structure Bounded.State (α : Type) where
  /--
  Queue of producers blocked waiting for buffer space to become available.
  -/
  producers : Std.Queue (IO.Promise Bool)

  /--
  Queue of consumers blocked waiting for new messages to be broadcast.
  -/
  waiters : Std.Queue (Broadcast.Consumer α)

  /--
  Maximum number of messages that can be buffered before producers block.
  -/
  capacity : { x : Nat // 0 < x }

  /--
  Current number of messages stored in the circular buffer.
  -/
  size : Nat

  /--
  Circular buffer storing broadcast messages accessible to all receivers.
  -/
  buffer : Vector (IO.Ref (Slot α)) capacity

  /--
  Index where the next message will be written in the circular buffer.
  -/
  write : Fin capacity

  /--
  Index of the oldest message still available for lagging receivers.
  -/
  read : Fin capacity

  /--
  Maps receiver IDs to their current position in the message sequence.
  -/
  receivers : Std.TreeMap Nat Nat

  /--
  Counter for assigning unique IDs to new receivers.
  -/
  nextId : Nat

  /--
  Whether the channel has been closed, preventing new messages.
  -/
  closed : Bool

  /--
  Global message sequence number for the next message to be sent.
  -/
  pos : Nat

/--
A channel that can create `Bounded.Receiver` and send messages.
-/
private structure Bounded (α : Type) where
  state : Mutex (Bounded.State α)

/--
A channel that can receive messages from `Bounded`.
-/
private structure Bounded.Receiver (α : Type) where
  state : Mutex (Bounded.State α)
  id : Nat

namespace Bounded

/--
Creates a new `Bounded` channel.
-/
private def new {α} (capacity : Nat := 16) (h : capacity > 0 := by decide) : BaseIO (Bounded α) := do
  return { state := ← Mutex.new {
    producers := .empty
    waiters := .empty
    buffer := ← Vector.mapM (fun _ => IO.mkRef { pos := 0, value := none, remaining := 0 }) (Vector.replicate capacity ())
    receivers := .empty
    nextId := 0
    closed := false
    pos := 0
    size := 0
    read := ⟨0, h⟩
    write := ⟨0, h⟩
    capacity := ⟨capacity, h⟩
  }}

/--
Subscribes a new `Receiver` in the `Bounded` channel.
-/
private def subscribe (bd : Bounded α) : IO (Receiver α) := do
  let id ← bd.state.atomically do
    modifyGet fun state =>
      let id := state.nextId
      (id, { state with nextId := id + 1, receivers := state.receivers.insert id state.pos })
  return { state := bd.state, id }

/--
Returns true if the buffer contains no elements.
-/
private def isEmpty [Monad m] [MonadLiftT (ST IO.RealWorld) m] : AtomicT (Bounded.State α) m Bool := do
  let mut st ← get
  return st.size = 0

/--
Returns true if the buffer is at full capacity.
-/
private def isFull : AtomicT (Bounded.State α) BaseIO Bool := do
  let mut st ← get
  return st.size ≥ st.capacity

/--
Enqueues an element to the back of the circular buffer.
If the buffer is full, the oldest element (at front) is overwritten.
-/
private def enqueue (value : α) (st : Bounded.State α) : BaseIO (Bounded.State α) := do
  let tailRef := st.buffer.get st.write

  tailRef.set { pos := st.pos, remaining := st.receivers.size, value := some value }
  let write : Fin st.capacity := @Fin.ofNat _ ⟨Nat.ne_zero_iff_zero_lt.mpr st.capacity.property⟩ (st.write + 1)
  let size := st.size + 1
  let pos := st.pos + 1

  return { st with write, size, pos }

/--
Dequeues an element from the front of the circular buffer.
Returns none if the buffer is empty.
-/
private def dequeue (st: State α) : State α :=
  let size := st.size - 1
  let read : Fin st.capacity := @Fin.ofNat _ ⟨Nat.ne_zero_iff_zero_lt.mpr st.capacity.property⟩ (st.read + 1)

  { st with read, size }

/--
Peeks at the element at the front of the buffer without removing it.
Returns none if the buffer is empty.
-/
private def getSlot
    [Monad m] [MonadLiftT (ST IO.RealWorld) m] (place : Nat) :
    AtomicT (Bounded.State α) m (IO.Ref (Slot α)) := do
  let st ← get
  let idx := (@Fin.ofNat st.capacity ⟨Nat.ne_zero_of_lt st.capacity.property⟩ place)
  return st.buffer.get idx

/--
Subscribes a new `Receiver` in the `Bounded` channel.
-/
private def trySend' (v : α) : AtomicT (Bounded.State α) BaseIO (Option Nat) := do
  if ← isFull then
    return none
  else
    let st ← enqueue v (← get)
    let waiters := st.waiters
    set ({ st with waiters := ∅ })

    for consumer in waiters.toArray do
      discard <| consumer.resolve true

    return some st.receivers.size

private def trySend (ch : Bounded α) (v : α) : BaseIO (Option Nat) := do
  ch.state.atomically do
    if (← get).closed then
      return none
    else if (← get).receivers.isEmpty then
      return (some 0)
    else
      trySend' v

private partial def send (ch : Bounded α) (v : α) : BaseIO (Task (Except Broadcast.Error Nat)) := do
  ch.state.atomically do
    if (← get).closed then
      return .pure <| .error .closed
    else if (← get).receivers.isEmpty then
      return .pure <| .ok 0
    else if let some receivers ← trySend' v then
      return .pure <| .ok receivers
    else
      let promise ← IO.Promise.new
      modify fun st => { st with producers := st.producers.enqueue promise }

      BaseIO.bindTask promise.result? fun res => do
        if res.getD false then
          Bounded.send ch v
        else
          return .pure <| .error .closed

private def close (ch : Bounded α) : EIO Broadcast.Error Unit := do
  ch.state.atomically do
    let st ← get

    if st.closed then
      throw .alreadyClosed

    for consumer in st.waiters.toArray do
      consumer.resolve false

    set { st with waiters := ∅, closed := true }
    return ()

private def isClosed (ch : Bounded α) : BaseIO Bool :=
  ch.state.atomically do
    return (← get).closed

namespace Receiver

private def getSlotValue [Monad m] [MonadLiftT (ST IO.RealWorld) m]
    (slot : IO.Ref (Slot α)) (next : Nat) : AtomicT (Bounded.State α) m (Option α × Bool) :=
  slot.modifyGet fun slot =>
    if next != slot.pos then
      ((none, false), slot)
    else if slot.remaining == 1 then
      ((slot.value, true), { slot with value := none, remaining := 0 })
    else
      ((slot.value, false), { slot with remaining := slot.remaining - 1 })

private def getValueByPosition [Monad m] [MonadLiftT (ST IO.RealWorld) m]
    [MonadLiftT BaseIO m] (next : Nat) : AtomicT (Bounded.State α) m (Option α) := do
  let mut st ← get

  if ← isEmpty then
    return none

  let id := next % st.capacity
  let slot ← getSlot id

  let (some val, shouldDequeue) ← getSlotValue slot next
    | return none

  if shouldDequeue then
    st := dequeue st

    if let some (producer, producers) := st.producers.dequeue? then
      producer.resolve true
      st := { st with producers }

  set st
  return some val

/--
Unsubscribes a `Receiver` from the `Bounded` channel.
-/
private def unsubscribe (bd : Bounded.Receiver α) : IO Unit := do
  let id ← bd.state.atomically do
    let st ← get

    let some next := st.receivers.get? bd.id
      | return Except.error Broadcast.Error.notSubscribed

    let mut currentSt := st
    let mut currentNext := next

    while currentNext < currentSt.pos ∧ currentSt.size > 0 do
      let some _val ← getValueByPosition currentNext | break

      currentSt ← get
      currentNext := currentNext + 1

    set { currentSt with receivers := currentSt.receivers.erase bd.id }

    pure <| .ok ()

  match id with
  | .error res => throw (.userError (toString res))
  | .ok _ => pure ()

private def tryRecv'
    [Monad m] [MonadLiftT (ST IO.RealWorld) m] [MonadLiftT BaseIO m]
    (receiverId : Nat) : AtomicT (Bounded.State α) m (Option α) := do
  let st ← get

  let some next := st.receivers[receiverId]?
    | return none

  if let some val ← getValueByPosition next then
    modify ({ · with receivers := st.receivers.modify receiverId (· + 1) })
    return some val
  else
    return none

private def tryRecv (ch : Bounded.Receiver α) : BaseIO (Option α) :=
  ch.state.atomically (tryRecv' ch.id)

private partial def recv (ch : Bounded.Receiver α) : BaseIO (Task (Option α)) := do
  ch.state.atomically do
    if ¬ (← get).receivers.contains ch.id then
      return .pure none
    else if let some val ← tryRecv' ch.id then
      return .pure <| some val
    else if (← get).closed then
      return .pure none
    else
      let promise ← IO.Promise.new
      modify fun st => { st with waiters := st.waiters.enqueue ⟨promise, none⟩ }
      BaseIO.bindTask promise.result? fun res => do
        if res.getD false then
          Bounded.Receiver.recv ch
        else
          return .pure none

private partial def forAsync
    (f : α → BaseIO Unit) (ch : Bounded.Receiver α)
    (prio : Task.Priority := .default) :
    BaseIO (Task Unit) := do
  BaseIO.bindTask (prio := prio) (← ch.recv) fun
    | none => return .pure ()
    | some v => do f v; forAsync f ch prio

@[inline]
private def recvReady'
    [Monad m] [MonadLiftT (ST IO.RealWorld) m] [MonadLiftT IO m] [MonadLiftT BaseIO m]
    (receiverId : Nat) : AtomicT (State α) m Bool := do
  let st ← get

  if st.closed then
    return true

  let some next := st.receivers.get? receiverId
    | return false

  if st.size = 0 then
    return false
  else
    let id := next % st.capacity
    let slot ← getSlot id
    let slotVal ← slot.get
    return slotVal.pos = next

open Internal.IO.Async in
private partial def recvSelector (ch : Bounded.Receiver α) : Selector (Option α) where
  tryFn := do
    ch.state.atomically do
      if ← recvReady' ch.id then
        let val ← tryRecv' ch.id
        return some val
      else
        return none

  registerFn waiter := registerAux ch waiter

  unregisterFn := do
    ch.state.atomically do
      let st ← get
      let waiters ← st.waiters.filterM fun c => do
        match c.waiter with
        | some waiter => return !(← waiter.checkFinished)
        | none => return true

      set { st with waiters }
where
  registerAux (ch : Bounded.Receiver α) (waiter : Waiter (Option α)) : IO Unit := do
    ch.state.atomically do
      if ← recvReady' ch.id then
        let lose := do
          let st ← get
          if let some (waiter, waiters) := st.waiters.dequeue? then
            waiter.resolve true
            set { st with waiters }
        let win promise := do
          promise.resolve (.ok (← tryRecv' ch.id))

        waiter.race lose win
      else
        let promise ← IO.Promise.new
        modify fun st => { st with waiters := st.waiters.enqueue ⟨promise, some waiter⟩ }

        IO.chainTask promise.result? fun res? => do
          match res? with
          | none => return ()
          | some res =>
            if res then
              registerAux ch waiter
            else
              let lose := return ()
              let win promise := promise.resolve (.ok none)
              waiter.race lose win

end Receiver
end Bounded

/--
A multi-subscriber broadcast that delivers each message to all current subscribers.
Supports only bounded buffering and an asynchronous API; to switch into
synchronous mode use `Broadcast.sync`.

Unlike `Std.Channel`, each message is received by **every** subscriber instead of just one.
Subscribers only receive messages sent after they have subscribed (unless otherwise specified).
-/
structure Broadcast (α : Type) where
  private mk ::
  private inner : Bounded α

/--
A receiver for a `Broadcast` channel that can asynchronously receive messages.
Each receiver gets a copy of every message sent to the broadcast channel after
the receiver was created. Multiple receivers can exist for the same broadcast,
and each will receive all messages independently.
-/
structure Broadcast.Receiver (α : Type) where
  private mk ::
  private inner : Bounded.Receiver α

namespace Broadcast

/--
Creates a new broadcast channel.
-/
@[inline]
def new {α} (capacity : Nat := 16) (h : capacity > 0 := by decide) : BaseIO (Broadcast α) := do
  return ⟨← Bounded.new capacity h⟩

/--
Try to send a value to the broadcast channel, if this can be completed right away without blocking return
`true`, otherwise don't send the value and return `false`.
-/
@[inline]
def trySend (ch : Broadcast α) (v : α) : BaseIO (Option Nat) :=
  ch.inner.trySend v

/--
Subscribes a new `Receiver` from the `Broadcast` channel.
-/
@[inline]
def subscribe (ch : Broadcast α) : IO (Broadcast.Receiver α) := do
  Broadcast.Receiver.mk <$> ch.inner.subscribe

/--
Closes a `Broadcast` channel.
-/
@[inline]
def close (ch : Broadcast α) : IO Unit := do
  ch.inner.close

/--
Send a value through the broadcast channel, returning a task that will resolve once the transmission
could be completed.
-/
@[inline]
def send (ch : Broadcast α) (v : α) : BaseIO (Task (Except IO.Error Nat)) := do
  BaseIO.bindTask (sync := true) (← ch.inner.send v)
    fun
      | .ok res => return .pure <| .ok res
      | .error err => return .pure <| .error (toString err)

namespace Receiver

/--
Try to receive a value from the broadcast receiver, if a message is available right away
return `some value`, otherwise return `none` without blocking.
-/
@[inline]
def tryRecv (ch : Broadcast.Receiver α) : BaseIO (Option α) :=
  Std.Bounded.Receiver.tryRecv ch.inner

/--
Receive a value from the broadcast receiver, returning a task that will resolve with
the next available message. This will block until a message is available.
-/
@[inline]
def recv [Inhabited α] (ch : Broadcast.Receiver α) : BaseIO (Task (Option α)) := do
  Std.Bounded.Receiver.recv ch.inner

open Internal.IO.Async in

/--
Creates a `Selector` that resolves once the broadcast channel `ch` has data available and provides that data.
-/
@[inline]
def recvSelector [Inhabited α] (ch : Broadcast.Receiver α) : Selector (Option α) :=
  Bounded.Receiver.recvSelector ch.inner

/--
Unsubscribes a `Receiver` from the `Broadcast` channel.
-/
@[inline]
def unsubscribe (ch : Broadcast.Receiver α) : IO Unit := do
  ch.inner.unsubscribe

/--
`ch.forAsync f` calls `f` for every message received on `ch`.

Note that if this function is called twice, each message will only arrive at exactly one invocation.
-/
partial def forAsync (f : α → BaseIO Unit) (ch : Broadcast.Receiver α)
    (prio : Task.Priority := .default) : BaseIO (Task Unit) := do
  ch.inner.forAsync f prio

instance [Inhabited α] : AsyncStream (Broadcast.Receiver α) (Option α) where
  next channel := channel.recvSelector
  stop channel := channel.unsubscribe

instance [Inhabited α] : AsyncRead (Broadcast.Receiver α) (Option α) where
  read receiver := Internal.IO.Async.Async.ofIOTask receiver.recv

instance [Inhabited α] : AsyncWrite (Broadcast α) α where
  write receiver x := do
    let task ← receiver.send x
    discard <| Async.ofTask <| task

end Receiver

/--
A multi-subscriber broadcast that delivers each message to all current subscribers.
Supports only bounded buffering and an asynchronous API.

It's the sync version of `Broadcast`.
-/
@[expose] def Sync (α : Type) : Type := Broadcast α

/--
A receiver for a `Broadcast` channel that can asynchronously receive messages.
Each receiver gets a copy of every message sent to the broadcast channel after
the receiver was created. Multiple receivers can exist for the same broadcast,
and each will receive all messages independently.

It's the sync version of `Broadcast.Receiver`.
-/
@[expose] def Sync.Receiver (α : Type) : Type := Broadcast.Receiver α

namespace Sync

@[inherit_doc Broadcast.new, inline]
def new (capacity : Nat := 16) (h : capacity > 0 := by decide) : BaseIO (Sync α) :=
  Broadcast.new capacity h

@[inherit_doc Broadcast.trySend, inline]
def trySend (ch : Sync α) (v : α) : BaseIO (Option Nat) :=
  Broadcast.trySend ch v

/--
Send a value through the channel, blocking until the transmission could be completed.
-/
@[inline]
def send (ch : Sync α) (v : α) : IO Nat := do
  IO.ofExcept =<< IO.wait (← Broadcast.send ch v)

namespace Receiver

@[inherit_doc Broadcast.Receiver.tryRecv, inline]
def tryRecv (ch : Sync.Receiver α) : BaseIO (Option α) := Broadcast.Receiver.tryRecv ch

/--
Receive a value from the channel, blocking until the transmission could be completed.
-/
def recv [Inhabited α] (ch : Sync.Receiver α) : BaseIO (Option α) := do
  IO.wait (← Broadcast.Receiver.recv ch)

partial def forIn [Inhabited α] [Monad m] [MonadLiftT BaseIO m]
    (ch : Sync.Receiver α) (f : α → β → m (ForInStep β)) : β → m β := fun b => do
  let a ← ch.recv
  match a with
  | none => pure b
  | some a =>
    match ← f a b with
    | .done b => pure b
    | .yield b => ch.forIn f b

/-- `for msg in ch.sync do ...` receives all messages in the channel until it is closed. -/
instance [Inhabited α] [Monad m] [MonadLiftT BaseIO m] : ForIn m (Sync.Receiver α) α where
  forIn ch b f := Receiver.forIn ch f b

end Receiver
end Sync
end Broadcast
end Std
