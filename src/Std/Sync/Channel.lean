/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Init.System.Promise
import Init.Data.Queue
import Std.Sync.Mutex

/-!
This module contains the implementation of `Std.Channel`. `Std.Channel` is a multi-producer
multi-consumer FIFO channel that offers both bounded and unbounded buffering as well as synchronous
and asynchronous APIs.

Additionally `Std.CloseableChannel` is provided in case closing the channel is of interest.
The two are distinct as the non closable `Std.Channel` can never throw errors which makes
for cleaner code.
-/

namespace Std

namespace CloseableChannel

/--
Errors that may be thrown while interacting with the channel API.
-/
inductive Error where
  /--
  Tried to send to a closed channel.
  -/
  | closed
  /--
  Tried to close an already closed channel.
  -/
  | alreadyClosed
deriving Repr, DecidableEq, Hashable

instance : ToString Error where
  toString
    | .closed => "trying to send on an already closed channel"
    | .alreadyClosed => "trying to close an already closed channel"

instance : MonadLift (EIO Error) IO where
  monadLift x := EIO.toIO (.userError <| toString ·) x

/--
The central state structure for an unbounded channel, maintains the following invariants:
1. `values = ∅ ∨ consumers = ∅`
2. `closed = true → consumers = ∅`
-/
private structure Unbounded.State (α : Type) where
  /--
  Values pushed into the channel that are waiting to be consumed.
  -/
  values : Std.Queue α
  /--
  Consumers that are blocked on a producer providing them a value. The `IO.Promise` will be
  resolved to `none` if the channel closes.
  -/
  consumers : Std.Queue (IO.Promise (Option α))
  /--
  Whether the channel is closed already.
  -/
  closed : Bool
deriving Nonempty

private structure Unbounded (α : Type) where
  state : Mutex (Unbounded.State α)
deriving Nonempty

namespace Unbounded

private def new : BaseIO (Unbounded α) := do
  return {
    state := ← Mutex.new {
      values := ∅
      consumers := ∅
      closed := false
    }
  }

private def trySend (ch : Unbounded α) (v : α) : BaseIO Bool := do
  ch.state.atomically do
    let st ← get
    if st.closed then
      return false
    else if let some (consumer, consumers) := st.consumers.dequeue? then
      consumer.resolve (some v)
      set { st with consumers }
      return true
    else
      set { st with values := st.values.enqueue v }
      return true

private def send (ch : Unbounded α) (v : α) : BaseIO (Task (Except Error Unit)) := do
  if ← Unbounded.trySend ch v then
    return .pure <| .ok ()
  else
    return .pure <| .error .closed

private def close (ch : Unbounded α) : EIO Error Unit := do
  ch.state.atomically do
    let st ← get
    if st.closed then throw .alreadyClosed
    for consumer in st.consumers.toArray do consumer.resolve none
    set { st with consumers := ∅, closed := true }
    return ()

private def isClosed (ch : Unbounded α) : BaseIO Bool :=
  ch.state.atomically do
    return (← get).closed

private def tryRecv' : AtomicT (Unbounded.State α) BaseIO (Option α) := do
  let st ← get
  if let some (a, values) := st.values.dequeue? then
    set { st with values }
    return some a
  else
    return none

private def tryRecv (ch : Unbounded α) : BaseIO (Option α) :=
  ch.state.atomically do
    tryRecv'

private def recv (ch : Unbounded α) : BaseIO (Task (Option α)) := do
  ch.state.atomically do
    if let some val ← tryRecv' then
      return .pure <| some val
    else if (← get).closed then
      return .pure none
    else
      let promise ← IO.Promise.new
      modify fun st => { st with consumers := st.consumers.enqueue promise }
      return promise.result?.map (sync := true) (·.bind id)

end Unbounded

/--
The central state structure for a zero buffer channel, maintains the following invariants:
1. `producers = ∅ ∨ consumers = ∅`
2. `closed = true → consumers = ∅`
-/
private structure Zero.State (α : Type) where
  /--
  Producers that are blocked on a consumer taking their value.
  -/
  producers : Std.Queue (α × IO.Promise Bool)
  /--
  Consumers that are blocked on a producer providing them a value. The `IO.Promise` will be resolved
  to `none` if the channel closes.
  -/
  consumers : Std.Queue (IO.Promise (Option α))
  /--
  Whether the channel is closed already.
  -/
  closed : Bool

private structure Zero (α : Type) where
  state : Mutex (Zero.State α)

namespace Zero

private def new : BaseIO (Zero α) := do
  return {
    state := ← Mutex.new {
      producers := ∅
      consumers := ∅
      closed := false
    }
  }

/--
Precondition: The channel must not be closed.
-/
private def trySend' (v : α) : AtomicT (Zero.State α) BaseIO Bool := do
  let st ← get
  if let some (consumer, consumers) := st.consumers.dequeue? then
    consumer.resolve (some v)
    set { st with consumers }
    return true
  else
    return false

private def trySend (ch : Zero α) (v : α) : BaseIO Bool := do
  ch.state.atomically do
    if (← get).closed then
      return false
    else
      trySend' v

private def send (ch : Zero α) (v : α) : BaseIO (Task (Except Error Unit)) := do
  ch.state.atomically do
    if (← get).closed then
      return .pure <| .error .closed
    else if ← trySend' v then
      return .pure <| .ok ()
    else
      let promise ← IO.Promise.new
      modify fun st => { st with producers := st.producers.enqueue (v, promise) }
      return promise.result?.map (sync := true)
        fun
          | none | some false => .error .closed
          | some true => .ok ()

private def close (ch : Zero α) : EIO Error Unit := do
  ch.state.atomically do
    let st ← get
    if st.closed then throw .alreadyClosed
    for consumer in st.consumers.toArray do consumer.resolve none
    set { st with consumers := ∅, closed := true }
    return ()

private def isClosed (ch : Zero α) : BaseIO Bool :=
  ch.state.atomically do
    return (← get).closed

private def tryRecv' : AtomicT (Zero.State α) BaseIO (Option α) := do
  let st ← get
  if let some ((val, promise), producers) := st.producers.dequeue? then
    set { st with producers }
    promise.resolve true
    return some val
  else
    return none

private def tryRecv (ch : Zero α) : BaseIO (Option α) := do
  ch.state.atomically do
    tryRecv'

private def recv (ch : Zero α) : BaseIO (Task (Option α)) := do
  ch.state.atomically do
    let st ← get
    if let some val ← tryRecv' then
      return .pure <| some val
    else if !st.closed then
      let promise ← IO.Promise.new
      set { st with consumers := st.consumers.enqueue promise }
      return promise.result?.map (sync := true) (·.bind id)
    else
      return .pure <| none

end Zero

/--
The central state structure for a bounded channel, maintains the following invariants:
1. `0 < capacity`
2. `0 < bufCount → consumers = ∅`
3. `bufCount < capacity → producers = ∅`
4. `producers = ∅ ∨ consumers = ∅`, implied by 1, 2 and 3.
5. `bufCount` corresponds to the amount of slots in `buf` that are `some`.
6. `sendIdx = (recvIdx + bufCount) % capacity`. However all four of these values still get tracked
   as there is potential to make a non-blocking send lock-free in the future with this approach.
7. `closed = true → consumers = ∅`

While it (currently) lacks the partial lock-freeness of go channels, the protocol is based on
[Go channels on steroids](https://docs.google.com/document/d/1yIAYmbvL3JxOKOjuCyon7JhW4cSv1wy5hC0ApeGMV9s/pub)
as well as its [implementation](https://go.dev/src/runtime/chan.go).
-/
private structure Bounded.State (α : Type) where
  /--
  Producers that are blocked on a consumer taking their value as there was no buffer space
  available when they tried to enqueue.
  -/
  producers : Std.Queue (IO.Promise Bool)
  /--
  Consumers that are blocked on a producer providing them a value, as there was no value
  enqueued when they tried to dequeue. The `IO.Promise` will be resolved to `false` if the channel
  closes.
  -/
  consumers : Std.Queue (IO.Promise Bool)
  /--
  The capacity of the buffer space.
  -/
  capacity : Nat
  /--
  The buffer space for the channel, slots with `some v` contain a value that is waiting for
  consumption, the slots with `none` are free for enqueueing.

  Note that this is a `Vector` of `IO.Ref (Option α)` as the `buf` itself is shared across threads
  and would thus keep getting copied if it was a `Vector (Option α)` instead.
  -/
  buf : Vector (IO.Ref (Option α)) capacity
  /--
  How many slots in `buf` are currently used, this is used to disambiguate between an empty and a
  full buffer without sacrificing a slot for indicating that.
  -/
  bufCount : Nat
  /--
  The slot in `buf` that the next send will happen to.
  -/
  sendIdx : Nat
  hsend : sendIdx < capacity
  /--
  The slot in `buf` that the next receive will happen from.
  -/
  recvIdx : Nat
  hrecv : recvIdx < capacity
  /--
  Whether the channel is closed already.
  -/
  closed : Bool

private structure Bounded (α : Type) where
  state : Mutex (Bounded.State α)

namespace Bounded

private def new (capacity : Nat) (hcap : 0 < capacity) : BaseIO (Bounded α) := do
  return {
    state := ← Mutex.new {
      producers := ∅
      consumers := ∅
      capacity := capacity
      buf := ← Vector.range capacity |>.mapM (fun _ => IO.mkRef none)
      bufCount := 0
      sendIdx := 0
      hsend := hcap
      recvIdx := 0
      hrecv := hcap
      closed := false
    }
  }

@[inline]
private def incMod (idx : Nat) (cap : Nat) : Nat :=
  if idx + 1 = cap then
    0
  else
    idx + 1

private theorem incMod_lt {idx cap : Nat} (h : idx < cap) : incMod idx cap < cap := by
  unfold incMod
  split <;> omega

/--
Precondition: The channel must not be closed.
-/
private def trySend' (v : α) : AtomicT (Bounded.State α) BaseIO Bool := do
  let mut st ← get
  if st.bufCount = st.capacity then
    return false
  else
    st.buf[st.sendIdx]'st.hsend |>.set (some v)
    st := { st with
      bufCount := st.bufCount + 1
      sendIdx := incMod st.sendIdx st.capacity
      hsend := incMod_lt st.hsend
    }

    if let some (consumer, consumers) := st.consumers.dequeue? then
      consumer.resolve true
      st := { st with consumers }

    set st

    return true

private def trySend (ch : Bounded α) (v : α) : BaseIO Bool := do
  ch.state.atomically do
    if (← get).closed then
      return false
    else
      trySend' v

private partial def send (ch : Bounded α) (v : α) : BaseIO (Task (Except Error Unit)) := do
  ch.state.atomically do
    if (← get).closed then
      return .pure <| .error .closed
    else if ← trySend' v then
      return .pure <| .ok ()
    else
      let promise ← IO.Promise.new
      modify fun st => { st with producers := st.producers.enqueue promise }
      BaseIO.bindTask promise.result? fun res => do
        if res.getD false then
          Bounded.send ch v
        else
          return .pure <| .error .closed

private def close (ch : Bounded α) : EIO Error Unit := do
  ch.state.atomically do
    let st ← get
    if st.closed then throw .alreadyClosed
    for consumer in st.consumers.toArray do consumer.resolve false
    set { st with consumers := ∅, closed := true }
    return ()

private def isClosed (ch : Bounded α) : BaseIO Bool :=
  ch.state.atomically do
    return (← get).closed

private def tryRecv' : AtomicT (Bounded.State α) BaseIO (Option α) := do
  let st ← get
  if st.bufCount == 0 then
    return none
  else
    let val ← st.buf[st.recvIdx]'st.hrecv |>.swap none
    let nextRecvIdx := incMod st.recvIdx st.capacity
    set { st with
      bufCount := st.bufCount - 1
      recvIdx := nextRecvIdx,
      hrecv := incMod_lt st.hrecv
    }
    return val

private def tryRecv (ch : Bounded α) : BaseIO (Option α) :=
  ch.state.atomically do
    tryRecv'

private partial def recv (ch : Bounded α) : BaseIO (Task (Option α)) := do
  ch.state.atomically do
    if let some val ← tryRecv' then
      let st ← get
      if let some (producer, producers) := (← get).producers.dequeue? then
        producer.resolve true
        set { st with producers }
      return .pure <| some val
    else if (← get).closed then
      return .pure none
    else
      let promise ← IO.Promise.new
      modify fun st => { st with consumers := st.consumers.enqueue promise }
      BaseIO.bindTask promise.result? fun res => do
        if res.getD false then
          Bounded.recv ch
        else
          return .pure none

end Bounded

/--
This type represents all flavors of channels that we have available.
-/
private inductive Flavors (α : Type) where
  | unbounded (ch : Unbounded α)
  | zero (ch : Zero α)
  | bounded (ch : Bounded α)
deriving Nonempty

end CloseableChannel

/--
A multi-producer multi-consumer FIFO channel that offers both bounded and unbounded buffering
and an asynchronous API, to switch into synchronous mode use `CloseableChannel.sync`.

Additionally `Std.CloseableChannel` can be closed if necessary, unlike `Std.Channel`.
This introduces a need for error handling in some cases, thus it is usually easier to use
`Std.Channel` if applicable.
-/
def CloseableChannel (α : Type) : Type := CloseableChannel.Flavors α

/--
A multi-producer multi-consumer FIFO channel that offers both bounded and unbounded buffering
and a synchronous API. This type acts as a convenient layer to use a channel in a blocking fashion
and is not actually different from the original channel.

Additionally `Std.CloseableChannel.Sync` can be closed if necessary, unlike `Std.Channel.Sync`.
This introduces the need to handle errors in some cases, thus it is usually easier to use
`Std.Channel` if applicable.
-/
def CloseableChannel.Sync (α : Type) : Type := CloseableChannel α

instance : Nonempty (CloseableChannel α) :=
  inferInstanceAs (Nonempty (CloseableChannel.Flavors α))

instance : Nonempty (CloseableChannel.Sync α) :=
  inferInstanceAs (Nonempty (CloseableChannel α))

namespace CloseableChannel

/--
Create a new channel, if:
- `capacity` is `none` it will be unbounded (the default)
- `capacity` is `some 0` it will always force a rendezvous between sender and receiver
- `capacity` is `some n` with `n > 0` it will use a buffer of size `n` and begin blocking once it
  is filled
-/
def new (capacity : Option Nat := none) : BaseIO (CloseableChannel α) := do
  match capacity with
  | none => return .unbounded (← CloseableChannel.Unbounded.new)
  | some 0 => return .zero (← CloseableChannel.Zero.new)
  | some (n + 1) => return .bounded (← CloseableChannel.Bounded.new (n + 1) (by omega))

/--
Try to send a value to the channel, if this can be completed right away without blocking return
`true`, otherwise don't send the value and return `false`.
-/
def trySend (ch : CloseableChannel α) (v : α) : BaseIO Bool :=
  match ch with
  | .unbounded ch => CloseableChannel.Unbounded.trySend ch v
  | .zero ch => CloseableChannel.Zero.trySend ch v
  | .bounded ch => CloseableChannel.Bounded.trySend ch v

/--
Send a value through the channel, returning a task that will resolve once the transmission could be
completed. Note that the task may resolve to `Except.error` if the channel was closed before it
could be completed.
-/
def send (ch : CloseableChannel α) (v : α) : BaseIO (Task (Except Error Unit)) :=
  match ch with
  | .unbounded ch => CloseableChannel.Unbounded.send ch v
  | .zero ch => CloseableChannel.Zero.send ch v
  | .bounded ch => CloseableChannel.Bounded.send ch v

/--
Closes the channel, returns `Except.ok` when called the first time, otherwise `Except.error`.
When a channel is closed:
- no new values can be sent successfully anymore
- all blocked consumers are resolved to `none` (as no new messages can be sent they will never
  resolve)
- if there are already values waiting to be received they can still be received by subsequent `recv`
  calls
-/
def close (ch : CloseableChannel α) : EIO Error Unit :=
  match ch with
  | .unbounded ch => CloseableChannel.Unbounded.close ch
  | .zero ch => CloseableChannel.Zero.close ch
  | .bounded ch => CloseableChannel.Bounded.close ch

/--
Return `true` if the channel is closed.
-/
def isClosed (ch : CloseableChannel α) : BaseIO Bool :=
  match ch with
  | .unbounded ch => CloseableChannel.Unbounded.isClosed ch
  | .zero ch => CloseableChannel.Zero.isClosed ch
  | .bounded ch => CloseableChannel.Bounded.isClosed ch

/--
Try to receive a value from the channel, if this can be completed right away without blocking return
`some value`, otherwise return `none`.
-/
def tryRecv (ch : CloseableChannel α) : BaseIO (Option α) :=
  match ch with
  | .unbounded ch => CloseableChannel.Unbounded.tryRecv ch
  | .zero ch => CloseableChannel.Zero.tryRecv ch
  | .bounded ch => CloseableChannel.Bounded.tryRecv ch

/--
Receive a value from the channel, returning a task that will resolve once the transmission could be
completed. Note that the task may resolve to `none` if the channel was closed before it could be
completed.
-/
def recv (ch : CloseableChannel α) : BaseIO (Task (Option α)) :=
  match ch with
  | .unbounded ch => CloseableChannel.Unbounded.recv ch
  | .zero ch => CloseableChannel.Zero.recv ch
  | .bounded ch => CloseableChannel.Bounded.recv ch

/--
`ch.forAsync f` calls `f` for every message received on `ch`.

Note that if this function is called twice, each message will only arrive at exactly one invocation.
-/
partial def forAsync (f : α → BaseIO Unit) (ch : CloseableChannel α)
    (prio : Task.Priority := .default) : BaseIO (Task Unit) := do
  BaseIO.bindTask (prio := prio) (← ch.recv) fun
    | none => return .pure ()
    | some v => do f v; ch.forAsync f prio

/--
This function is a no-op and just a convenient way to expose the synchronous API of the channel.
-/
@[inline]
def sync (ch : CloseableChannel α) : CloseableChannel.Sync α := ch

namespace Sync

@[inherit_doc CloseableChannel.new, inline]
def new (capacity : Option Nat := none) : BaseIO (Sync α) := CloseableChannel.new capacity

@[inherit_doc CloseableChannel.trySend, inline]
def trySend (ch : Sync α) (v : α) : BaseIO Bool := CloseableChannel.trySend ch v

/--
Send a value through the channel, blocking until the transmission could be completed. Note that this
function may throw an error when trying to send to an already closed channel.
-/
def send (ch : Sync α) (v : α) : EIO Error Unit := do
  EIO.ofExcept (← IO.wait (← CloseableChannel.send ch v))

@[inherit_doc CloseableChannel.close, inline]
def close (ch : Sync α) : EIO Error Unit := CloseableChannel.close ch

@[inherit_doc CloseableChannel.isClosed, inline]
def isClosed (ch : Sync α) : BaseIO Bool := CloseableChannel.isClosed ch

@[inherit_doc CloseableChannel.tryRecv, inline]
def tryRecv (ch : Sync α) : BaseIO (Option α) := CloseableChannel.tryRecv ch

/--
Receive a value from the channel, blocking unitl the transmission could be completed. Note that the
return value may be `none` if the channel was closed before it could be completed.
-/
def recv (ch : Sync α) : BaseIO (Option α) := do
  IO.wait (← CloseableChannel.recv ch)

private partial def forIn [Monad m] [MonadLiftT BaseIO m]
    (ch : Sync α) (f : α → β → m (ForInStep β)) : β → m β := fun b => do
  match ← ch.recv with
  | some a =>
    match ← f a b with
    | .done b => pure b
    | .yield b => ch.forIn f b
  | none => pure b

/-- `for msg in ch.sync do ...` receives all messages in the channel until it is closed. -/
instance [MonadLiftT BaseIO m] : ForIn m (Sync α) α where
  forIn ch b f := ch.forIn f b

end Sync

end CloseableChannel

/--
A multi-producer multi-consumer FIFO channel that offers both bounded and unbounded buffering
and an asynchronous API, to switch into synchronous mode use `Channel.sync`.

If a channel needs to be closed to indicate some sort of completion event use `Std.CloseableChannel`
instead. Note that `Std.CloseableChannel` introduces a need for error handling in some cases, thus
`Std.Channel` is usually easier to use if applicable.
-/
structure Channel (α : Type) where
  private mk ::
    private inner : CloseableChannel α
deriving Nonempty

/--
A multi-producer multi-consumer FIFO channel that offers both bounded and unbounded buffering
and a synchronous API. This type acts as a convenient layer to use a channel in a blocking fashion
and is not actually different from the original channel.

If a channel needs to be closed to indicate some sort of completion event use
`Std.CloseableChannel.Sync` instead. Note that `Std.CloseableChannel.Sync` introduces a need for error
handling in some cases, thus `Std.Channel.Sync` is usually easier to use if applicable.
-/
def Channel.Sync (α : Type) : Type := Channel α

instance : Nonempty (Channel.Sync α) :=
  inferInstanceAs (Nonempty (Channel α))

namespace Channel

@[inherit_doc CloseableChannel.new, inline]
def new (capacity : Option Nat := none) : BaseIO (Channel α) := do
  return ⟨← CloseableChannel.new capacity⟩

@[inherit_doc CloseableChannel.trySend, inline]
def trySend (ch : Channel α) (v : α) : BaseIO Bool :=
  CloseableChannel.trySend ch.inner v

/--
Send a value through the channel, returning a task that will resolve once the transmission could be
completed.
-/
def send (ch : Channel α) (v : α) : BaseIO (Task Unit) := do
  BaseIO.bindTask (sync := true) (← CloseableChannel.send ch.inner v)
    fun
      | .ok .. => return .pure ()
      | .error .. => unreachable!

@[inherit_doc CloseableChannel.tryRecv, inline]
def tryRecv (ch : Channel α) : BaseIO (Option α) :=
  CloseableChannel.tryRecv ch.inner

@[inherit_doc CloseableChannel.recv]
def recv [Inhabited α] (ch : Channel α) : BaseIO (Task α) := do
  BaseIO.bindTask (sync := true) (← CloseableChannel.recv ch.inner)
    fun
      | some val => return .pure val
      | none => unreachable!

@[inherit_doc CloseableChannel.forAsync]
partial def forAsync [Inhabited α] (f : α → BaseIO Unit) (ch : Channel α)
    (prio : Task.Priority := .default) : BaseIO (Task Unit) := do
  BaseIO.bindTask (prio := prio) (← ch.recv) fun v => do f v; ch.forAsync f prio

@[inherit_doc CloseableChannel.sync, inline]
def sync (ch : Channel α) : Channel.Sync α := ch

namespace Sync

@[inherit_doc Channel.new, inline]
def new (capacity : Option Nat := none) : BaseIO (Sync α) := Channel.new capacity

@[inherit_doc Channel.trySend, inline]
def trySend (ch : Sync α) (v : α) : BaseIO Bool := Channel.trySend ch v

/--
Send a value through the channel, blocking until the transmission could be completed.
-/
def send (ch : Sync α) (v : α) : BaseIO Unit := do
  IO.wait (← Channel.send ch v)

@[inherit_doc Channel.tryRecv, inline]
def tryRecv (ch : Sync α) : BaseIO (Option α) := Channel.tryRecv ch

/--
Receive a value from the channel, blocking unitl the transmission could be completed.
-/
def recv [Inhabited α] (ch : Sync α) : BaseIO α := do
  IO.wait (← Channel.recv ch)

private partial def forIn [Inhabited α] [Monad m] [MonadLiftT BaseIO m]
    (ch : Sync α) (f : α → β → m (ForInStep β)) : β → m β := fun b => do
  let a ← ch.recv
  match ← f a b with
  | .done b => pure b
  | .yield b => ch.forIn f b

/-- `for msg in ch.sync do ...` receives all messages in the channel until it is closed. -/
instance [Inhabited α] [MonadLiftT BaseIO m] : ForIn m (Sync α) α where
  forIn ch b f := ch.forIn f b

end Sync

end Channel

end Std
