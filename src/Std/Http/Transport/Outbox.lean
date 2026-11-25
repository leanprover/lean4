/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Http.Transport
public import Std.Async.Watchdog

public section

/-!
# Outbox

An `Outbox` writes a connection's output to its transport in order, without the connection waiting
for each write.
-/

namespace Std.Http.Internal

open Std Async

set_option linter.all true

/--
The state of an `Outbox`.
-/
structure Outbox.State where
  /--
  Output handed over while a write was in flight, newest first, written together once it
  completes. A list, because the state is shared with the thread that completes the write, so an
  array here would be copied on every append.
  -/
  queued : List (Array ByteArray) := []

  /--
  The size of `queued` in bytes.
  -/
  queuedBytes : Nat := 0

  /--
  A write is in flight.
  -/
  writing : Bool := false

  /--
  A write failed, so later output is dropped.
  -/
  failed : Bool := false

  /--
  The error of the failed write, until it is taken.
  -/
  error : Option IO.Error := none

  /--
  Resolved once no write is in flight.
  -/
  idle : Option (IO.Promise Unit) := none

/--
Writes a connection's output to `socket` in order without the connection waiting for it. At most
one write is in flight. Output handed over meanwhile goes out in a single write once that write
completes, started by the thread that completed it.
-/
structure Outbox (α : Type) where
  private mk ::

  /--
  The transport the output is written to.
  -/
  socket : α

  /--
  How long, in milliseconds, a wait for output to be written lasts without any write completing
  before the outbox fails.
  -/
  writeTimeout : Nat

  private state : IO.Ref Outbox.State

  /--
  Cancelled by `watchdog` once a write in flight has seen none complete for `writeTimeout`, and by
  `stop`.
  -/
  private writeContext : CancellationContext

  /--
  Armed while a write is in flight. Only the code that starts a write or handles its completion arms
  or disarms it, so its calls follow the writes' order.
  -/
  private watchdog : Watchdog

namespace Outbox

/--
Creates an outbox that writes to `socket`, failing a wait for its writes once none has completed for
`writeTimeout` milliseconds. `stop` releases its timer.
-/
def new (socket : α) (writeTimeout : Nat) : IO (Outbox α) := do
  let writeContext ← CancellationContext.new
  return {
    socket, writeTimeout, writeContext
    state := ← IO.mkRef {}
    watchdog := ← Watchdog.new writeContext
  }

/--
Releases the outbox's timer. A wait for its writes then no longer times out.
-/
def stop (outbox : Outbox α) : BaseIO Unit :=
  outbox.writeContext.cancel .cancel

/--
Joins queued output, given newest first, into one write in order.
-/
private def joinQueued : List (Array ByteArray) → Array ByteArray
  | [batch] => batch
  | batches => batches.foldr (fun batch acc => acc ++ batch) #[]

/--
Starts writing `data`, then whatever was queued meanwhile once the write completes. For a socket,
the next write thus starts on the event loop's own thread.
-/
private partial def write [Transport α] (outbox : Outbox α) (data : Array ByteArray) :
    BaseIO Unit := do
  let task ← EAsync.toBaseIO (Transport.sendAll outbox.socket data)
  BaseIO.chainTask (sync := true) task fun result => do
    -- Disarm before giving up `writing`: a `send` that then starts a write arms after this.
    if result matches .error _ || (← outbox.state.get).queued.isEmpty then
      discard <| outbox.watchdog.disarm
    let (next, idle) ← outbox.state.modifyGet fun s =>
      match result with
      | .error err =>
        ((#[], s.idle), { s with
          queued := [], queuedBytes := 0, writing := false, failed := true, error := some err
          idle := none })
      | .ok () =>
        if s.queued.isEmpty then
          ((#[], s.idle), { s with writing := false, idle := none })
        else ((joinQueued s.queued, none), { s with queued := [], queuedBytes := 0 })
    if let some idle := idle then
      idle.resolve ()
    unless next.isEmpty do
      outbox.watchdog.arm (.ofNat outbox.writeTimeout)
      outbox.write next

/--
Hands `buffer` to the outbox, which writes it after everything handed over before. Returns how many
bytes now wait behind the write in flight, or `none` if a write failed and `buffer` was dropped.
-/
def send [Transport α] (outbox : Outbox α) (buffer : ChunkedBuffer) : BaseIO (Option Nat) := do
  if buffer.size = 0 then
    return if (← outbox.state.get).failed then none else some 0
  let data := buffer.data
  let (start, queued?) ← outbox.state.modifyGet fun s =>
    if s.failed then ((false, none), s)
    else if s.writing then
      let queuedBytes := s.queuedBytes + buffer.size
      ((false, some queuedBytes), { s with queued := data :: s.queued, queuedBytes })
    else ((true, some 0), { s with writing := true })
  if start then
    outbox.watchdog.arm (.ofNat outbox.writeTimeout)
    outbox.write data
    -- A write that fails without suspending has already dropped `buffer`.
    if (← outbox.state.get).failed then
      return none
  return queued?

/--
Returns `true` while a write is in flight.
-/
def writing (outbox : Outbox α) : BaseIO Bool :=
  return (← outbox.state.get).writing

/--
A task that finishes once no write is in flight, or `none` if none is or the outbox failed.
-/
def idle? (outbox : Outbox α) : BaseIO (Option (Task (Option Unit))) := do
  let s ← outbox.state.get
  if !s.writing || s.failed then
    return none
  let fresh ← IO.Promise.new
  outbox.state.modifyGet fun s =>
    if !s.writing || s.failed then (none, s)
    else match s.idle with
      | some idle => (some idle.result?, s)
      | none => (some fresh.result?, { s with idle := some fresh })

/--
Fails the outbox because its peer stopped reading: queued output is dropped and later output too.
The write in flight stays in flight until the transport completes it or is closed.
-/
private def expire (outbox : Outbox α) : BaseIO Unit :=
  outbox.state.modify fun s =>
    if s.failed then s
    else { s with
      failed := true, queued := [], queuedBytes := 0
      error := some (IO.userError s!"no write completed within {outbox.writeTimeout} ms") }

/--
A selector that fires once `task` finishes.
-/
private def taskSelector (task : Task (Option Unit)) : Selector Unit where
  tryFn := do
    if ← IO.hasFinished task then return some () else return none
  registerFn waiter :=
    BaseIO.chainTask (sync := true) task fun _ =>
      waiter.race (pure ()) (fun promise => promise.resolve (.ok ()))
  unregisterFn := pure ()

/--
A selector that fires once a write in flight has seen no write complete for `writeTimeout`, or once
the outbox is stopped. A wait for the writes, such as `awaitIdle`, then fails the outbox.
-/
def lateSelector (outbox : Outbox α) : Selector Unit :=
  outbox.writeContext.doneSelector

/--
Waits until no write is in flight. If no write completes for `writeTimeout` milliseconds meanwhile,
the outbox fails instead, so a peer that stops reading cannot hold the connection.
-/
def awaitIdle (outbox : Outbox α) : Async Unit := do
  let some idle ← outbox.idle? | return
  let finished ← Selectable.one #[
    .case (taskSelector idle) (fun _ => pure true),
    .case outbox.lateSelector (fun _ => pure false)]
  if !finished && (← outbox.watchdog.hasFired) then
    outbox.expire

/--
Returns `true` once a write failed.
-/
def failed (outbox : Outbox α) : BaseIO Bool :=
  return (← outbox.state.get).failed

/--
Waits until every write handed over so far completed. Returns `false` if a write failed or none
completed within `writeTimeout`.
-/
def awaitWritten (outbox : Outbox α) : Async Bool := do
  outbox.awaitIdle
  return !(← outbox.failed)

/--
Takes the error of the failed write, so that only the first caller gets it.
-/
def takeError? (outbox : Outbox α) : BaseIO (Option IO.Error) :=
  outbox.state.modifyGet fun s => (s.error, { s with error := none })

/--
Hands `buffer` to the outbox, then waits for its writes if more than `limit` bytes are queued, so a
peer that does not read holds up the caller instead of growing its memory. Returns `false` if a
write failed or none completed within `writeTimeout`.
-/
def push [Transport α] (outbox : Outbox α) (buffer : ChunkedBuffer) (limit : Nat := 65536) :
    Async Bool := do
  match ← outbox.send buffer with
  | some queued =>
    if queued ≤ limit then
      return true
    outbox.awaitWritten
  | none => return false

end Outbox

end Std.Http.Internal
