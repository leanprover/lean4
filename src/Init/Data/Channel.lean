/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
prelude
import Init.Data.Queue
import Init.System.Promise
import Init.System.Mutex

namespace IO

/--
Internal state of an `Channel`.

We maintain the invariant that at all times either `consumers` or `values` is empty.
-/
structure Channel.State (α : Type) where
  values : Std.Queue α := ∅
  consumers : Std.Queue (Promise (Option α)) := ∅
  closed := false
  deriving Inhabited

/--
FIFO channel with a receive operation returning a `Task`.

A channel can be closed.  Once it is closed, all `send`s are ignored, and
`recvAsync` returns `none` once the queue is empty.
-/
def Channel (α : Type) : Type := Mutex (Channel.State α)

instance : Nonempty (Channel α) :=
  inferInstanceAs (Nonempty (Mutex _))

/-- Creates a new `Channel`. -/
def Channel.new : BaseIO (Channel α) :=
  Mutex.new {}

/--
Sends a message on an `Channel`.

This function does not block.
-/
def Channel.send (v : α) (ch : Channel α) : BaseIO Unit :=
  ch.atomically do
    let st ← get
    if st.closed then return
    if let some (consumer, consumers) := st.consumers.dequeue? then
      consumer.resolve (some v)
      set { st with consumers }
    else
      set { st with values := st.values.enqueue v }

/--
Closes an `Channel`.
-/
def Channel.close (ch : Channel α) : BaseIO Unit :=
  ch.atomically do
    let st ← get
    for consumer in st.consumers.toArray do consumer.resolve none
    set { st with closed := true, consumers := ∅ }

/--
Receives a message.

Returns `none` if the channel is closed and the queue is empty.
-/
def Channel.recvAsync (ch : Channel α) : BaseIO (Task (Option α)) :=
  ch.atomically do
    let st ← get
    if let some (a, values) := st.values.dequeue? then
      set { st with values }
      return .pure a
    else if !st.closed then
      let promise ← Promise.new
      set { st with consumers := st.consumers.enqueue promise }
      return promise.result
    else
      return .pure none

/--
`ch.forAsync f` calls `f` for every messages received on `ch`.

Note that if this function is called twice, each `forAsync` only gets half the messages.
-/
partial def Channel.forAsync (f : α → BaseIO Unit) (ch : Channel α)
    (prio : Task.Priority := .default) : BaseIO (Task Unit) := do
  BaseIO.bindTask (prio := prio) (← ch.recvAsync) fun
    | none => return .pure ()
    | some v => do f v; ch.forAsync f prio
