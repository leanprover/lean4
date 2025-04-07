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
-/

namespace Std
namespace Experimental

namespace Channel

/--
The central state structure for unbounded channels, maintains the following invariants:
1. `values = ∅ ∨ consumers = ∅`.
2. `closed = true → consumers = ∅`.
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

private def send (ch : Unbounded α) (v : α) : BaseIO (Task (Option Unit)) := do
  if ← Unbounded.trySend ch v then
    return .pure <| some ()
  else
    return .pure <| none

private def close (ch : Unbounded α) : BaseIO (Option Unit) := do
  ch.state.atomically do
    let st ← get
    if st.closed then return none
    for consumer in st.consumers.toArray do consumer.resolve none
    set { st with consumers := ∅, closed := true }
    return some ()

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
The central state structure for zero buffer channels, maintains the following invariants:
1. `producers = ∅ ∨ consumers = ∅`.
2. `closed = true → producers = ∅ ∧ consumers = ∅`.
-/
private structure Zero.State (α : Type) where
  /--
  Producers that are blocked on a consumer taking their value. The `IO.Promise` will be resolved
  to `false` if the channel closes.
  -/
  producers : Std.Queue (α × IO.Promise Bool)
  /--
  Consumers that are blocked on a producer providing them a value. The `IO.Promise` will be resolved
  to `false` if the channel closes.
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

private def send (ch : Zero α) (v : α) : BaseIO (Task (Option Unit)) := do
  ch.state.atomically do
    if (← get).closed then
      return .pure none
    else if ← trySend' v then
      return .pure <| some ()
    else
      let promise ← IO.Promise.new
      modify fun st => { st with producers := st.producers.enqueue (v, promise) }
      return promise.result?.map (sync := true) discard

private def close (ch : Zero α) : BaseIO (Option Unit) := do
  ch.state.atomically do
    let st ← get
    if st.closed then return none
    for consumer in st.consumers.toArray do consumer.resolve none
    set { st with consumers := ∅, closed := true }
    return some ()

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
The central state structure for unbounded channels, maintains the following invariants:
1. `0 < capacity`
2. `0 < bufCount → consumers = ∅`
3. `bufCount < capacity → producers = ∅`
4. `producers = ∅ ∨ consumers = ∅`, implied by 1, 2 and 3.
5. `bufCount` corresponds to the amount of slots in `buf` that are `some`.
6. `closed = true → producers = ∅ ∧ consumers = ∅`

While it (currently) lacks the partial lock-freeness of go channels, the protocol is based on
[Go channels on steroids](https://docs.google.com/document/d/1yIAYmbvL3JxOKOjuCyon7JhW4cSv1wy5hC0ApeGMV9s/pub)
as well as its [implementation](https://go.dev/src/runtime/chan.go).
-/
private structure Bounded.State (α : Type) where
  /--
  Producers that are blocked on a consumer taking their value as there wasn't any buffer space
  available when they tried to enqueue. The `IO.Promise` will be resolved to `false` if the channel
  closes.
  -/
  producers : Std.Queue (IO.Promise Bool)
  /--
  Consumers that are blocked on a producer providing them a value, as there wasn't any value
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
  -/
  buf : Vector (Option α) capacity
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
      buf := Vector.replicate capacity none
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
  let success ← modifyGet fun st =>
    if st.bufCount == st.capacity then
      (false, st)
    else
      let st := { st with
        buf := st.buf.set st.sendIdx (some v) st.hsend
        bufCount := st.bufCount + 1
        sendIdx := incMod st.sendIdx st.capacity
        hsend := incMod_lt st.hsend
      }
      (true, st)
      let st ← get

  if success then
    if let some (consumer, consumers) := st.consumers.dequeue? then
      consumer.resolve true
      set { st with consumers }

    return true
  else
    return false

private def trySend (ch : Bounded α) (v : α) : BaseIO Bool := do
  ch.state.atomically do
    if (← get).closed then
      return false
    else
      trySend' v

private partial def send (ch : Bounded α) (v : α) : BaseIO (Task (Option Unit)) := do
  ch.state.atomically do
    if (← get).closed then
      return .pure none
    else if ← trySend' v then
      return .pure <| some ()
    else
      let promise ← IO.Promise.new
      modify fun st => { st with producers := st.producers.enqueue promise }
      BaseIO.bindTask promise.result? fun res => do
        if res.getD false then
          Bounded.send ch v
        else
          return .pure none

private def close (ch : Bounded α) : BaseIO (Option Unit) := do
  ch.state.atomically do
    let st ← get
    if st.closed then return none
    for consumer in st.consumers.toArray do consumer.resolve false
    set { st with consumers := ∅, closed := true : State α }
    return some ()

private def isClosed (ch : Bounded α) : BaseIO Bool :=
  ch.state.atomically do
    return (← get).closed

private def tryRecv' : AtomicT (Bounded.State α) BaseIO (Option α) :=
  modifyGet fun st =>
    if st.bufCount == 0 then
      (none, st)
    else
      let val := st.buf[st.recvIdx]'st.hrecv
      let nextRecvIdx := incMod st.recvIdx st.capacity
      let st := { st with
        buf := st.buf.set st.recvIdx none st.hrecv,
        bufCount := st.bufCount - 1
        recvIdx := nextRecvIdx,
        hrecv := incMod_lt st.hrecv
      }
      (val, st)

private def tryRecv (ch : Bounded α) : BaseIO (Option α) :=
  ch.state.atomically do
    tryRecv'

private partial def recv (ch : Bounded α) : BaseIO (Task (Option α)) := do
  ch.state.atomically do
    if let some val ← tryRecv' then
      -- Receive succeeded, see if we need to unblock a producer.
      let st ← get
      if let some (producer, producers) := (← get).producers.dequeue? then
        producer.resolve true
        set { st with producers }
      return .pure <| some val
    else if (← get).closed then
      return .pure none
    else
      -- The channel is empty.
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

end Channel

/--
A multi-producer multi-consumer FIFO channel that offers both bounded and unbounded buffering
and an asynchronous API, to switch into synchronous mode use `Channel.sync`.
-/
def Channel (α : Type) : Type := Channel.Flavors α

/--
A multi-producer multi-consumer FIFO channel that offers both bounded and unbounded buffering
and a synchronous API, can be obtained from a `Channel` through `Channel.sync`
-/
def Channel.Sync (α : Type) : Type := Channel α

instance : Nonempty (Channel α) := inferInstanceAs (Nonempty (Channel.Flavors α))
instance : Nonempty (Channel.Sync α) := inferInstanceAs (Nonempty (Channel α))

namespace Channel

-- TODO: Think about whether keeping none just for backwards compat is right.

/--
Create a new `Channel`, if:
- `capacity` is `none` it will be unbounded.
- `capacity` is `some 0` it will always force a rendezvous between sender and receiver.
- `capacity` is `some n` with `n > 0` it will use a buffer of size `n` and begin blocking once it
  is filled.
-/
def new (capacity : Option Nat := none) : BaseIO (Channel α) := do
  match capacity with
  | none => return .unbounded (← Channel.Unbounded.new)
  | some 0 => return .zero (← Channel.Zero.new)
  | some (n + 1) => return .bounded (← Channel.Bounded.new (n + 1) (by omega))

/--
Try to send a value to the channel, if this can be completed right away without blocking return
`true`, otherwise don't send the value and return `false`.
-/
def trySend (ch : Channel α) (v : α) : BaseIO Bool :=
  match ch with
  | .unbounded ch => Channel.Unbounded.trySend ch v
  | .zero ch => Channel.Zero.trySend ch v
  | .bounded ch => Channel.Bounded.trySend ch v

/--
Send a value through the channel, returning a task that will resolve once the transmission could be
completed. Note that the task may resolve to `none` if the channel was closed before it could be
completed.
-/
def send (ch : Channel α) (v : α) : BaseIO (Task (Option Unit)) :=
  match ch with
  | .unbounded ch => Channel.Unbounded.send ch v
  | .zero ch => Channel.Zero.send ch v
  | .bounded ch => Channel.Bounded.send ch v

/--
Closes the channel, returns `some ()` when called the first time, otherwise `none`.
When a channel is closed:
- no new values can be sent successfully anymore
- all blocked consumers are resolved to `none` (as no new messages can be sent they will never
  resolve)
- if there is still values waiting to be received they can still be received by subsequent `recv`
  calls
-/
def close (ch : Channel α) : BaseIO (Option Unit) :=
  match ch with
  | .unbounded ch => Channel.Unbounded.close ch
  | .zero ch => Channel.Zero.close ch
  | .bounded ch => Channel.Bounded.close ch

/--
Return `true` if the channel is closed.
-/
def isClosed (ch : Channel α) : BaseIO Bool :=
  match ch with
  | .unbounded ch => Channel.Unbounded.isClosed ch
  | .zero ch => Channel.Zero.isClosed ch
  | .bounded ch => Channel.Bounded.isClosed ch

/--
Try to receive a value from the channel, if this can be completed right away without blocking return
`some value`, otherwise return `none`.
-/
def tryRecv (ch : Channel α) : BaseIO (Option α) :=
  match ch with
  | .unbounded ch => Channel.Unbounded.tryRecv ch
  | .zero ch => Channel.Zero.tryRecv ch
  | .bounded ch => Channel.Bounded.tryRecv ch

/--
Receive a value from the channel, returning a task that will resolve once the transmission could be
completed. Note that the task may resolve to `none` if the channel was closed before it could be
completed.
-/
def recv (ch : Channel α) : BaseIO (Task (Option α)) :=
  match ch with
  | .unbounded ch => Channel.Unbounded.recv ch
  | .zero ch => Channel.Zero.recv ch
  | .bounded ch => Channel.Bounded.recv ch

/--
`ch.forAsync f` calls `f` for every messages received on `ch`.

Note that if this function is called twice, each message will only arrive at exactly one invocation.
-/
partial def forAsync (f : α → BaseIO Unit) (ch : Channel α)
    (prio : Task.Priority := .default) : BaseIO (Task Unit) := do
  BaseIO.bindTask (prio := prio) (← ch.recv) fun
    | none => return .pure ()
    | some v => do f v; ch.forAsync f prio

/--
This function is a no-op and just a convenient way to expose the synchronous API of the channel.
-/
def sync (ch : Channel α) : Channel.Sync α := ch

namespace Sync

@[inherit_doc Channel.new]
def new (capacity : Option Nat := none) : BaseIO (Sync α) := Channel.new capacity

@[inherit_doc Channel.trySend]
def trySend (ch : Sync α) (v : α) : BaseIO Bool := Channel.trySend ch v

/--
Send a value through the channel, blocking until the transmission could be completed. Note that the
task may resolve to `none` if the channel was closed before it could be completed.
-/
def send (ch : Sync α) (v : α) : BaseIO (Option Unit) := do
  IO.wait (← Channel.send ch v)

@[inherit_doc Channel.close]
def close (ch : Sync α) : BaseIO (Option Unit) := Channel.close ch

@[inherit_doc Channel.isClosed]
def isClosed (ch : Sync α) : BaseIO Bool := Channel.isClosed ch

@[inherit_doc Channel.tryRecv]
def tryRecv (ch : Sync α) : BaseIO (Option α) := Channel.tryRecv ch

/--
Receive a value from the channel, blocking unitl the transmission could be completed. Note that the
task may resolve to `none` if the channel was closed before it could be completed.
-/
def recv (ch : Sync α) : BaseIO (Option α) := do
  IO.wait (← Channel.recv ch)

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

end Channel

end Experimental
end Std
