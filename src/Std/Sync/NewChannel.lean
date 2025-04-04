/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Gabriel Ebner
-/
prelude
import Init.System.Promise
import Init.Data.Queue
import Std.Sync.Mutex

namespace Std
namespace Experimental

namespace Channel
-- TODO: Better queue
-- TODO: think about whether we can unlock earlier in some places
-- TODO: think about closed fast path more

private structure Unbounded.State (α : Type) where
  values : Std.Queue α := ∅
  consumers : Std.Queue (IO.Promise (Option α)) := ∅
deriving Nonempty

private structure Unbounded (α : Type) where
  state : Mutex (Unbounded.State α)
  -- invariant: `closed` only written to while holding state mutex, read is fine.
  -- invariant: if `closed` is true then `state.consumers` is empty
  closed : IO.Ref Bool
deriving Nonempty

namespace Unbounded

def new : BaseIO (Unbounded α) := do
  return {
    state := ← Mutex.new {}
    closed := ← IO.mkRef false
  }

def send (ch : Unbounded α) (v : α) : BaseIO (Task (Option Unit)) := do
  -- fast path
  if ← ch.closed.get then return .pure none
  ch.state.atomically do
    -- might have raced
    if ← ch.closed.get then return .pure none
    let st ← get
    if let some (consumer, consumers) := st.consumers.dequeue? then
      consumer.resolve (some v)
      set { st with consumers }
      return .pure <| some ()
    else
      set { st with values := st.values.enqueue v }
      return .pure <| some ()

def close (ch : Unbounded α) : BaseIO Unit := do
  ch.state.atomically do
    -- might be already closed
    if ← ch.closed.get then return ()
    let st ← get
    for consumer in st.consumers.toArray do consumer.resolve none
    set { st with consumers := ∅ }
    ch.closed.set true

def recv (ch : Unbounded α) : BaseIO (Task (Option α)) := do
  ch.state.atomically do
    let st ← get
    if let some (a, values) := st.values.dequeue? then
      set { st with values }
      return .pure a
    else if !(← ch.closed.get) then
      let promise ← IO.Promise.new
      set { st with consumers := st.consumers.enqueue promise }
      return promise.result?.map (sync := true) (·.bind id)
    else
      return .pure <| none

end Unbounded

private structure Zero.State (α : Type) where
  producers : Std.Queue (α × IO.Promise (Option Unit)) := ∅
  consumers : Std.Queue (IO.Promise (Option α)) := ∅
deriving Nonempty

private structure Zero (α : Type) where
  state : Mutex (Zero.State α)
  -- invariant: `closed` only written to while holding state mutex, read is fine.
  -- invariant: if `closed` is true then `state.consumers` and `state.producers` are empty
  closed : IO.Ref Bool
deriving Nonempty

namespace Zero

def new : BaseIO (Zero α) := do
  return {
    state := ← Mutex.new {}
    closed := ← IO.mkRef false
  }

def send (ch : Zero α) (v : α) : BaseIO (Task (Option Unit)) := do
  -- fast path
  if ← ch.closed.get then return .pure none
  ch.state.atomically do
    -- might have raced
    if ← ch.closed.get then return .pure none
    let st ← get
    if let some (consumer, consumers) := st.consumers.dequeue? then
      consumer.resolve (some v)
      set { st with consumers }
      return .pure <| some ()
    else
      let promise ← IO.Promise.new
      set { st with producers := st.producers.enqueue (v, promise) }
      return promise.result?.map (sync := true) (·.bind id)

def close (ch : Zero α) : BaseIO Unit := do
  ch.state.atomically do
    -- might be already closed
    if ← ch.closed.get then return ()
    let st ← get
    for consumer in st.consumers.toArray do consumer.resolve none
    for producer in st.producers.toArray do producer.2.resolve none
    set { st with consumers := ∅, producers := ∅ : State α }
    ch.closed.set true

def recv (ch : Zero α) : BaseIO (Task (Option α)) := do
  ch.state.atomically do
    let st ← get
    if let some ((val, promise), producers) := st.producers.dequeue? then
      set { st with producers }
      promise.resolve (some ())
      return .pure val
    else if !(← ch.closed.get) then
      let promise ← IO.Promise.new
      set { st with consumers := st.consumers.enqueue promise }
      return promise.result?.map (sync := true) (·.bind id)
    else
      return .pure <| none

end Zero

private inductive Flavors (α : Type) where
  | unbounded (ch : Unbounded α)
  | zero (ch : Zero α)
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
  -- TODO:
  | some _ => return .unbounded (← Channel.Unbounded.new)

def send (ch : Channel α) (v : α) : BaseIO (Task (Option Unit)) :=
  match ch with
  | .unbounded ch => Channel.Unbounded.send ch v
  | .zero ch => Channel.Zero.send ch v

-- TODO: should close on a closed channel indicate a failure mode?
def close (ch : Channel α) : BaseIO Unit :=
  match ch with
  | .unbounded ch => Channel.Unbounded.close ch
  | .zero ch => Channel.Zero.close ch

def recv (ch : Channel α) : BaseIO (Task (Option α)) :=
  match ch with
  | .unbounded ch => Channel.Unbounded.recv ch
  | .zero ch => Channel.Zero.recv ch

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
