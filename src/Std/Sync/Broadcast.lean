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

/-!
This module contains the implementation of `Std.Broadcast`. `Std.Broadcast` provides a
broadcasting primitive for sending values to multiple consumers. It maintains a queue of
values and supports both synchronous and asynchronous waiting.
-/

namespace Std

inductive Error where
  | closed
  | alreadyClosed
  | noSubscribers

instance : ToString Error where
  toString
    | .closed => "trying to send on an already closed channel"
    | .alreadyClosed => "trying to close an already closed broadcast channel"
    | .noSubscribers => "there are no subscribers"

instance : MonadLift (EIO Error) IO where
  monadLift x := EIO.toIO (.userError <| toString ·) x

open Internal.IO.Async in

/--

-/
structure Broadcast.Consumer (α : Type) where
  promise : IO.Promise Bool
  waiter : Option (Waiter (Option α))

/--

-/
def Broadcast.Consumer.resolve (c : Broadcast.Consumer α) (b : Bool) : BaseIO Unit :=
  c.promise.resolve b

/--

-/
private structure Slot (α : Type) where
  value : Option α
  pos : Nat
  remaining : Nat
deriving Nonempty, Inhabited, Repr

/--
State of the channel.
-/
structure Broadcast.State (α : Type) where

  /--
  Producers that are waiting for a chance to write because the buffer is full.
  -/
  producers : Std.Queue (IO.Promise Bool)

  /--
  Consumers that are waiting for a chance to receive the last available value, because
  they consumed all the ones that were available.
  -/
  waiters : Std.Queue (Broadcast.Consumer α)

  /--
  The capacity of the entire buffer.
  -/
  capacity : { x : Nat // x > 0 }

  /--
  The size of the entire buffer.
  -/
  size : Nat

  /--
  Circular buffer for storing the data that was sent.
  -/
  public buffer : Vector (IO.Ref (Slot α)) capacity

  /--
  The write pointer of the buffer
  -/
  write : Fin capacity

  /--
  The write pointer of the buffer
  -/
  read : Fin capacity

  /--
  Map from id to index.
  -/
  receivers : Std.TreeMap Nat Nat

  /--
  The next id for the next receiver
  -/
  nextId : Nat

  /--
  Flag if the channel is closed.
  -/
  closed : Bool

  /--
  Position
  -/
  pos : Nat

  /--
  Mask
  -/
  mask : Nat

/--
A channel that can create `Broadcast.Receiver` and send messages.
-/
structure ClosableBroadcast (α : Type) where
  state : Mutex (Broadcast.State α)

/--
A channel that can receive messages from `Broadcast`.
-/
structure ClosableBroadcast.Receiver (α : Type) where
  state : Mutex (Broadcast.State α)
  id : Nat

/--
A channel that can create `Broadcast.Receiver` and send messages.
-/
public def Broadcast := ClosableBroadcast


/--
A channel that can receive messages from `Broadcast`.
-/
public def Broadcast.Receiver := ClosableBroadcast.Receiver

namespace Broadcast

def bitLength : Nat → Nat
  | 0 => 0
  | n + 1 => 1 + bitLength ((n + 1) / 2)

def nextPowerOfTwo (n : Nat) : Nat :=
  if n = 0 then 0
  else if n = 1 then 1
  else 1 <<< (bitLength (n - 1))

theorem shiftLeft_pos (m : Nat) : 1 <<< m > 0 := by
  rw [Nat.shiftLeft_eq]
  simp only [Nat.one_mul]
  exact Nat.pow_pos (by decide)

theorem nextPowerOfTwo_gt_zero_when_pos : n > 0 → nextPowerOfTwo n > 0 := by
  intro h
  simp [nextPowerOfTwo]
  split
  · omega
  · split
    · decide
    · exact shiftLeft_pos _

/--
Creates a new `Broadcast` Channel.
-/
public def new (capacity : Nat := 16) (h : capacity > 0 := by decide) : BaseIO (Broadcast α) := do
  let capacity := nextPowerOfTwo capacity

  return { state := ← Mutex.new {
    producers := .empty
    waiters := .empty
    buffer := ← Vector.mapM (fun _ => IO.mkRef { pos := 0, value := none, remaining := 0 }) (Vector.replicate capacity ())
    receivers := .empty
    nextId := 0
    closed := false
    pos := 0
    size := 0
    mask := capacity - 1
    read := ⟨0, nextPowerOfTwo_gt_zero_when_pos h⟩
    write := ⟨0, nextPowerOfTwo_gt_zero_when_pos h⟩
    capacity := ⟨capacity, nextPowerOfTwo_gt_zero_when_pos h⟩
  }}

/--
Subscribes a new `Receiver` in the `Broadcast` channel.
-/
public def subscribe (bd : Broadcast α) : IO (Receiver α) := do
  let id ← bd.state.atomically do
    modifyGet fun state =>
      let id := state.nextId
      (id, { state with nextId := id + 1, receivers := state.receivers.insert id state.pos })
  return { state := bd.state, id }

/-- Returns true if the buffer contains no elements. -/
def isEmpty [Monad m] [MonadLiftT (ST IO.RealWorld) m] [MonadLiftT IO m] [MonadLiftT BaseIO m] : AtomicT (Broadcast.State α) m Bool := do
  let mut st ← get
  return st.size = 0

/-- Returns true if the buffer is at full capacity. -/
def isFull : AtomicT (Broadcast.State α) BaseIO Bool := do
  let mut st ← get
  return st.size ≥ st.capacity

/--
Enqueues an element to the back of the circular buffer.
If the buffer is full, the oldest element (at front) is overwritten.
-/
def enqueue [Nonempty α] (value : α) (st : Broadcast.State α) : BaseIO (Broadcast.State α) := do
  let tailRef := st.buffer.get st.write

  tailRef.set { pos := st.pos, remaining := st.receivers.size, value := some value }

  let size := st.size + 1
  let write : Fin st.capacity := @Fin.ofNat _ ⟨Nat.ne_zero_iff_zero_lt.mpr st.capacity.property⟩ (st.write + 1)

  return { st with write, size, pos := st.pos + 1 }

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
def getSlot
  [Monad m] [MonadLiftT (ST IO.RealWorld) m] [MonadLiftT IO m] [MonadLiftT BaseIO m] (place : Nat) :
  AtomicT (Broadcast.State α) m (IO.Ref (Slot α)) := do
    let mut st ← get
    let idx := (@Fin.ofNat st.capacity ⟨Nat.ne_zero_of_lt st.capacity.property⟩ place)
    return st.buffer.get idx

/--
Subscribes a new `Receiver` in the `Broadcast` channel.
-/
def trySend' [Nonempty α] (v : α) : AtomicT (Broadcast.State α) BaseIO Bool := do
  if ← isFull then
    return false
  else
    let mut st ← enqueue v (← get)
    let mut waiters := st.waiters
    set ({ st with waiters := ∅ })

    for consumer in waiters.toArray do
      discard <| consumer.resolve true

    return true

def trySend [Nonempty α] (ch : Broadcast α) (v : α) : BaseIO Bool := do
  ch.state.atomically do
    if (← get).closed then
      return false
    else
      trySend' v

public partial def send [Nonempty α] (ch : Broadcast α) (v : α) : BaseIO (Task (Except Error Unit)) := do
  ch.state.atomically do
    if (← get).closed then
      return .pure <| .error .closed
    else if (← get).receivers.isEmpty then
      return .pure <| .error .noSubscribers
    else if ← trySend' v then
      return .pure <| .ok ()
    else
      let promise ← IO.Promise.new
      modify fun st => { st with producers := st.producers.enqueue promise }

      BaseIO.bindTask promise.result? fun res => do
        if res.getD false then
          Broadcast.send ch v
        else
          return .pure <| .error .closed

def close (ch : Broadcast α) : EIO Error Unit := do
  ch.state.atomically do
    let st ← get

    if st.closed then
      throw .alreadyClosed

    for consumer in st.waiters.toArray do
      consumer.resolve false

    set { st with waiters := ∅, closed := true }
    return ()

def isClosed (ch : Broadcast α) : BaseIO Bool :=
  ch.state.atomically do
    return (← get).closed


namespace Receiver

def getSlotValue
  [Monad m] [MonadLiftT (ST IO.RealWorld) m] [MonadLiftT IO m] [MonadLiftT BaseIO m]
  (slot : IO.Ref (Slot α)) (next : Nat) : AtomicT (Broadcast.State α) m (Option α × Bool) :=
    slot.modifyGet fun slot =>
      if next != slot.pos then
        ((none, false), slot)
      else if slot.remaining == 1 then
        ((slot.value, true), { slot with value := none, remaining := 0 })
      else
        ((slot.value, false), { slot with remaining := slot.remaining - 1 })

def tryRecv'
  [Monad m] [MonadLiftT (ST IO.RealWorld) m] [MonadLiftT IO m] [MonadLiftT BaseIO m]
  (receiverId : Nat) : AtomicT (Broadcast.State α) m (Option α) := do
    let mut st ← get

    if ← isEmpty then
      return none

    let next := st.receivers.get! receiverId
    let id := next &&& st.mask

    let slot ← getSlot id

    let (some val, shouldDequeue) ← getSlotValue slot next
      | return none

    if shouldDequeue then
      st := dequeue st

      if let some (producer, producers) := st.producers.dequeue? then
        producer.resolve true
        st := { st with producers }

    set { st with receivers := st.receivers.modify receiverId (· + 1) }

    return some val

def tryRecv (ch : Broadcast.Receiver α) : IO (Option α) :=
  ch.state.atomically do
    tryRecv' ch.id

public partial def recv (ch : Broadcast.Receiver α) : IO (Task (Except IO.Error (Option α))) := do
  ch.state.atomically do
    if let some val ← tryRecv' ch.id then
      return .pure <| .ok <| some val
    else if (← get).closed then
      return .pure <| .ok none
    else
      let promise ← IO.Promise.new
      modify fun st => { st with waiters := st.waiters.enqueue ⟨promise, none⟩ }
      IO.bindTask promise.result? fun res => do
        if res.getD false then
          Broadcast.Receiver.recv ch
        else
          return .pure (.ok none)
