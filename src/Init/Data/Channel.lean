/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
prelude
import Init.Data.Queue
import Init.System.Promise
import Init.System.Mutex

set_option linter.deprecated false

namespace IO

/--
Internal state of a `Channel`.

We maintain the invariant that at all times either `consumers` or `values` is empty.
-/
@[deprecated "Use Std.Channel.State from Std.Sync.Channel instead" (since := "2024-12-02")]
structure Channel.State (α : Type) where
  values : Std.Queue α := ∅
  consumers : Std.Queue (Promise (Option α)) := ∅
  closed := false
  deriving Inhabited

/--
FIFO channel with unbounded buffer, where `recv?` returns a `Task`.

A channel can be closed. Once it is closed, all `send`s are ignored, and
`recv?` returns `none` once the queue is empty.
-/
@[deprecated "Use Std.Channel from Std.Sync.Channel instead" (since := "2024-12-02")]
def Channel (α : Type) : Type := Mutex (Channel.State α)

instance : Nonempty (Channel α) :=
  inferInstanceAs (Nonempty (Mutex _))

/-- Creates a new `Channel`. -/
@[deprecated "Use Std.Channel.new from Std.Sync.Channel instead" (since := "2024-12-02")]
def Channel.new : BaseIO (Channel α) :=
  Mutex.new {}

/--
Sends a message on a `Channel`.

This function does not block.
-/
@[deprecated "Use Std.Channel.send from Std.Sync.Channel instead" (since := "2024-12-02")]
def Channel.send (ch : Channel α) (v : α) : BaseIO Unit :=
  ch.atomically do
    let st ← get
    if st.closed then return
    if let some (consumer, consumers) := st.consumers.dequeue? then
      consumer.resolve (some v)
      set { st with consumers }
    else
      set { st with values := st.values.enqueue v }

/--
Closes a `Channel`.
-/
@[deprecated "Use Std.Channel.close from Std.Sync.Channel instead" (since := "2024-12-02")]
def Channel.close (ch : Channel α) : BaseIO Unit :=
  ch.atomically do
    let st ← get
    for consumer in st.consumers.toArray do consumer.resolve none
    set { st with closed := true, consumers := ∅ }

/--
Receives a message, without blocking.
The returned task waits for the message.
Every message is only received once.

Returns `none` if the channel is closed and the queue is empty.
-/
@[deprecated "Use Std.Channel.recv? from Std.Sync.Channel instead" (since := "2024-12-02")]
def Channel.recv? (ch : Channel α) : BaseIO (Task (Option α)) :=
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
@[deprecated "Use Std.Channel.forAsync from Std.Sync.Channel instead" (since := "2024-12-02")]
partial def Channel.forAsync (f : α → BaseIO Unit) (ch : Channel α)
    (prio : Task.Priority := .default) : BaseIO (Task Unit) := do
  BaseIO.bindTask (prio := prio) (← ch.recv?) fun
    | none => return .pure ()
    | some v => do f v; ch.forAsync f prio

/--
Receives all currently queued messages from the channel.

Those messages are dequeued and will not be returned by `recv?`.
-/
@[deprecated "Use Std.Channel.recvAllCurrent from Std.Sync.Channel instead" (since := "2024-12-02")]
def Channel.recvAllCurrent (ch : Channel α) : BaseIO (Array α) :=
  ch.atomically do
    modifyGet fun st => (st.values.toArray, { st with values := ∅ })

/-- Type tag for synchronous (blocking) operations on a `Channel`. -/
@[deprecated "Use Std.Channel.Sync from Std.Sync.Channel instead" (since := "2024-12-02")]
def Channel.Sync := Channel

/--
Accesses synchronous (blocking) version of channel operations.

For example, `ch.sync.recv?` blocks until the next message,
and `for msg in ch.sync do ...` iterates synchronously over the channel.
These functions should only be used in dedicated threads.
-/
@[deprecated "Use Std.Channel.sync from Std.Sync.Channel instead" (since := "2024-12-02")]
def Channel.sync (ch : Channel α) : Channel.Sync α := ch

/--
Synchronously receives a message from the channel.

Every message is only received once.
Returns `none` if the channel is closed and the queue is empty.
-/
@[deprecated "Use Std.Channel.Sync.recv? from Std.Sync.Channel instead" (since := "2024-12-02")]
def Channel.Sync.recv? (ch : Channel.Sync α) : BaseIO (Option α) := do
  IO.wait (← Channel.recv? ch)

@[deprecated "Use Std.Channel.Sync.forIn from Std.Sync.Channel instead" (since := "2024-12-02")]
private partial def Channel.Sync.forIn [Monad m] [MonadLiftT BaseIO m]
    (ch : Channel.Sync α) (f : α → β → m (ForInStep β)) : β → m β := fun b => do
  match ← ch.recv? with
    | some a =>
      match ← f a b with
        | .done b => pure b
        | .yield b => ch.forIn f b
    | none => pure b

/-- `for msg in ch.sync do ...` receives all messages in the channel until it is closed. -/
instance [MonadLiftT BaseIO m] : ForIn m (Channel.Sync α) α where
  forIn ch b f := ch.forIn f b
