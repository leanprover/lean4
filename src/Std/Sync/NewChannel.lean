/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Gabriel Ebner
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

private structure Unbounded.State (α : Type) where
  values : Std.Queue α := ∅
  consumers : Std.Queue (IO.Promise (Option α)) := ∅
  -- invariant: if `closed` is true then `consumers` is empty
  closed : Bool := false
deriving Nonempty

private structure Unbounded (α : Type) where
  state : Mutex (Unbounded.State α)
deriving Nonempty

namespace Unbounded

def new : BaseIO (Unbounded α) := do
  return {
    state := ← Mutex.new {}
  }

def send (ch : Unbounded α) (v : α) : BaseIO (Task (Option Unit)) := do
  ch.state.atomically do
    -- might have raced
    let st ← get
    if st.closed then
      return .pure none
    else if let some (consumer, consumers) := st.consumers.dequeue? then
      consumer.resolve (some v)
      set { st with consumers }
      return .pure <| some ()
    else
      set { st with values := st.values.enqueue v }
      return .pure <| some ()

def close (ch : Unbounded α) : BaseIO Unit := do
  ch.state.atomically do
    let st ← get
    if st.closed then return ()
    for consumer in st.consumers.toArray do consumer.resolve none
    set { st with consumers := ∅, closed := true }

def recv (ch : Unbounded α) : BaseIO (Task (Option α)) := do
  ch.state.atomically do
    let st ← get
    if let some (a, values) := st.values.dequeue? then
      set { st with values }
      return .pure <| some a
    else if !st.closed then
      let promise ← IO.Promise.new
      set { st with consumers := st.consumers.enqueue promise }
      return promise.result?.map (sync := true) (·.bind id)
    else
      return .pure none

end Unbounded

private structure Zero.State (α : Type) where
  producers : Std.Queue (α × IO.Promise (Option Unit)) := ∅
  consumers : Std.Queue (IO.Promise (Option α)) := ∅
  -- invariant: if `closed` is true then `consumers` and `producers` are empty
  closed : Bool := false
deriving Nonempty

private structure Zero (α : Type) where
  state : Mutex (Zero.State α)
deriving Nonempty

namespace Zero

def new : BaseIO (Zero α) := do
  return {
    state := ← Mutex.new {}
  }

def send (ch : Zero α) (v : α) : BaseIO (Task (Option Unit)) := do
  ch.state.atomically do
    let st ← get
    if st.closed then
      return .pure none
    else if let some (consumer, consumers) := st.consumers.dequeue? then
      consumer.resolve (some v)
      set { st with consumers }
      return .pure <| some ()
    else
      let promise ← IO.Promise.new
      set { st with producers := st.producers.enqueue (v, promise) }
      return promise.result?.map (sync := true) (·.bind id)

def close (ch : Zero α) : BaseIO Unit := do
  ch.state.atomically do
    let st ← get
    if st.closed then return ()
    for consumer in st.consumers.toArray do consumer.resolve none
    for producer in st.producers.toArray do producer.2.resolve none
    set { st with consumers := ∅, producers := ∅, closed := true : State α }

def recv (ch : Zero α) : BaseIO (Task (Option α)) := do
  ch.state.atomically do
    let st ← get
    if let some ((val, promise), producers) := st.producers.dequeue? then
      set { st with producers }
      promise.resolve (some ())
      return .pure <| some val
    else if !st.closed then
      let promise ← IO.Promise.new
      set { st with consumers := st.consumers.enqueue promise }
      return promise.result?.map (sync := true) (·.bind id)
    else
      return .pure <| none

end Zero

private structure Bounded.State (α : Type) where
  producers : Std.Queue (IO.Promise Bool) := ∅
  consumers : Std.Queue (IO.Promise Bool) := ∅
  capacity : Nat
  buf : Vector (Option α) capacity
  bufCount : Nat
  sendIdx : Nat
  hsend : sendIdx < capacity
  recvIdx : Nat
  hrecv : recvIdx < capacity
  -- invariant: if `closed` is true then `consumers` and `producers` are empty
  closed : Bool := false

private structure Bounded (α : Type) where
  state : Mutex (Bounded.State α)

namespace Bounded

def new (capacity : Nat) (hcap : 0 < capacity) : BaseIO (Bounded α) := do
  return {
    state := ← Mutex.new {
      capacity := capacity
      buf := Vector.replicate capacity none
      bufCount := 0
      sendIdx := 0
      hsend := hcap
      recvIdx := 0
      hrecv := hcap
    }
  }

@[inline]
def incMod (idx : Nat) (cap : Nat) : Nat :=
  if idx + 1 = cap then
    0
  else
    idx + 1

theorem incMod_lt {idx cap : Nat} (h : idx < cap) : incMod idx cap < cap := by
  unfold incMod
  split <;> omega

def trySend' (v : α) : AtomicT (Bounded.State α) BaseIO Bool :=
  modifyGet fun st =>
    if st.bufCount == st.capacity then
      (false, st)
    else
      let nextSendIdx := incMod st.sendIdx st.capacity
      let st := { st with
        buf := st.buf.set st.sendIdx (some v) st.hsend,
        bufCount := st.bufCount + 1
        sendIdx := nextSendIdx,
        hsend := incMod_lt st.hsend
      }
      (true, st)

partial def send (ch : Bounded α) (v : α) : BaseIO (Task (Option Unit)) := do
  ch.state.atomically do
    if (← get).closed then
      return .pure none
    else if ← trySend' v then
      -- Send succeeded, see if we need to unblock a consumer.
      let st ← get
      if let some (consumer, consumers) := (← get).consumers.dequeue? then
        consumer.resolve true
        set { st with consumers }
      return .pure <| some ()
    else
      -- The channel is full.
      let promise ← IO.Promise.new
      modify fun st => { st with producers := st.producers.enqueue promise }
      BaseIO.bindTask promise.result? fun res => do
        if res.getD false then
          Bounded.send ch v
        else
          return .pure none

def close (ch : Bounded α) : BaseIO Unit := do
  ch.state.atomically do
    let st ← get
    if st.closed then return ()
    for consumer in st.consumers.toArray do consumer.resolve false
    for producer in st.producers.toArray do producer.resolve false
    set { st with consumers := ∅, producers := ∅, closed := true : State α }

def tryRecv' : AtomicT (Bounded.State α) BaseIO (Option α) :=
  modifyGet fun st =>
    if st.bufCount == 0 then
      (none, st)
    else
      -- TODO: show with an invariant that this is never none
      let val := st.buf[st.recvIdx]'st.hrecv
      let nextRecvIdx := incMod st.recvIdx st.capacity
      let st := { st with
        buf := st.buf.set st.recvIdx none st.hrecv,
        bufCount := st.bufCount - 1
        recvIdx := nextRecvIdx,
        hrecv := incMod_lt st.hrecv
      }
      (val, st)

partial def recv (ch : Bounded α) : BaseIO (Task (Option α)) := do
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

private inductive Flavors (α : Type) where
  | unbounded (ch : Unbounded α)
  | zero (ch : Zero α)
  | bounded (ch : Bounded α)
deriving Nonempty

end Channel

def Channel (α : Type) : Type := Channel.Flavors α
def Channel.Sync (α : Type) : Type := Channel α

instance : Nonempty (Channel α) := inferInstanceAs (Nonempty (Channel.Flavors α))
instance : Nonempty (Channel.Sync α) := inferInstanceAs (Nonempty (Channel α))

namespace Channel

-- TODO: Think about whether keeping none just for backwards compat is right.
def new (capacity : Option Nat := none) : BaseIO (Channel α) := do
  match capacity with
  | none => return .unbounded (← Channel.Unbounded.new)
  | some 0 => return .zero (← Channel.Zero.new)
  | some (n + 1) => return .bounded (← Channel.Bounded.new (n + 1) (by omega))

def send (ch : Channel α) (v : α) : BaseIO (Task (Option Unit)) :=
  match ch with
  | .unbounded ch => Channel.Unbounded.send ch v
  | .zero ch => Channel.Zero.send ch v
  | .bounded ch => Channel.Bounded.send ch v

-- TODO: should close on a closed channel indicate a failure mode?
def close (ch : Channel α) : BaseIO Unit :=
  match ch with
  | .unbounded ch => Channel.Unbounded.close ch
  | .zero ch => Channel.Zero.close ch
  | .bounded ch => Channel.Bounded.close ch

def recv (ch : Channel α) : BaseIO (Task (Option α)) :=
  match ch with
  | .unbounded ch => Channel.Unbounded.recv ch
  | .zero ch => Channel.Zero.recv ch
  | .bounded ch => Channel.Bounded.recv ch

partial def forAsync (f : α → BaseIO Unit) (ch : Channel α)
    (prio : Task.Priority := .default) : BaseIO (Task Unit) := do
  BaseIO.bindTask (prio := prio) (← ch.recv) fun
    | none => return .pure ()
    | some v => do f v; ch.forAsync f prio

def sync (ch : Channel α) : Channel.Sync α := ch

namespace Sync

def new (capacity : Option Nat := none) : BaseIO (Sync α) := Channel.new capacity

def send (ch : Sync α) (v : α) : BaseIO (Option Unit) := do
  IO.wait (← Channel.send ch v)

def close (ch : Sync α) : BaseIO Unit := Channel.close ch

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
