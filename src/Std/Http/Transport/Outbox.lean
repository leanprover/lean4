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
The timer of an `Outbox`, which tells when the write in flight has seen no write complete for
`writeTimeout`. A watchdog stays fired once it fires, so once a late write completes the timer is
replaced and the next write is timed afresh.
-/
structure Outbox.Timer where
  /--
  Cancelled by `watchdog` once the write in flight runs late, and by `stop`.
  -/
  ctx : CancellationContext

  /--
  Armed while a write is in flight. Only the code that starts a write or handles its completion arms
  or disarms it, so its calls follow the writes' order.
  -/
  watchdog : Watchdog

  /--
  The outbox was stopped, so the timer is not replaced again.
  -/
  stopped : Bool := false

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

  /--
  The most bytes one write carries, if bounded. Each completed write renews the write timeout, so a
  bound makes `writeTimeout` limit each pause of a long write rather than the whole of it.
  -/
  maxWriteBytes : Option Nat := none

  private state : IO.Ref Outbox.State

  /--
  The current timer. Only the code that handles a write's completion replaces it.
  -/
  private timer : IO.Ref Outbox.Timer

namespace Outbox

private def Timer.new : IO Outbox.Timer := do
  let ctx ← CancellationContext.new
  return { ctx, watchdog := ← Watchdog.new ctx }

/--
Creates an outbox that writes to `socket`, failing a wait for its writes once none has completed for
`writeTimeout` milliseconds. `stop` releases its timer.
-/
def new (socket : α) (writeTimeout : Nat) (maxWriteBytes : Option Nat := none) : IO (Outbox α) := do
  return {
    socket, writeTimeout, maxWriteBytes, state := ← IO.mkRef {}, timer := ← IO.mkRef (← Timer.new) }

/--
Releases the outbox's timer. A wait for its writes then no longer times out.
-/
def stop (outbox : Outbox α) : BaseIO Unit := do
  let timer ← outbox.timer.modifyGet fun t => (t, { t with stopped := true })
  timer.ctx.cancel .cancel

/--
Replaces the timer after it fired, once the write that ran late completed, so the next write is
timed afresh. Does nothing once the outbox is stopped.
-/
private def renew (outbox : Outbox α) : BaseIO Unit := do
  let .ok fresh ← Timer.new.toBaseIO | return
  let installed ← outbox.timer.modifyGet fun t => if t.stopped then (false, t) else (true, fresh)
  unless installed do
    fresh.ctx.cancel .cancel

/--
Joins queued output, given newest first, into one write in order.
-/
private def joinQueued : List (Array ByteArray) → Array ByteArray
  | [batch] => batch
  | batches => batches.foldr (fun batch acc => acc ++ batch) #[]

/--
Splits `data` into the first write, of at most `limit` bytes when bounded, and the rest.
-/
private def split (limit : Option Nat) (data : Array ByteArray) : Array ByteArray × Array ByteArray :=
  match limit with
  | none => (data, #[])
  | some limit =>
    let (now, rest, _) := data.foldl (init := (#[], #[], 0)) fun (now, rest, size) bytes =>
      if !rest.isEmpty || size ≥ limit then (now, rest.push bytes, size)
      else if size + bytes.size ≤ limit then (now.push bytes, rest, size + bytes.size)
      else
        let cut := limit - size
        (now.push (bytes.extract 0 cut), rest.push (bytes.extract cut bytes.size), limit)
    (now, rest)

/--
The bytes `data` holds.
-/
private def byteSize (data : Array ByteArray) : Nat :=
  data.foldl (· + ·.size) 0

/--
Starts writing `data`, then whatever was queued meanwhile once the write completes. For a socket,
the next write thus starts on the event loop's own thread.
-/
private partial def write [Transport α] (outbox : Outbox α) (data : Array ByteArray) :
    BaseIO Unit := do
  let task ← EAsync.toBaseIO (Transport.sendAll outbox.socket data)
  BaseIO.chainTask (sync := true) task fun result => do
    -- Settle the timer before giving up `writing`: a `send` that then starts a write arms after this.
    -- `disarm` decides lateness atomically, so the watchdog cannot fire between this and the next
    -- write's `arm`, which would leave that write under a fired timer.
    if ← (← outbox.timer.get).watchdog.disarm then
      outbox.renew
    let (next, idle) ← outbox.state.modifyGet fun s =>
      match result with
      | .error err =>
        ((#[], s.idle), { s with
          queued := [], queuedBytes := 0, writing := false, failed := true, error := some err
          idle := none })
      | .ok () =>
        if s.queued.isEmpty then
          ((#[], s.idle), { s with writing := false, idle := none })
        else
          let (next, rest) := split outbox.maxWriteBytes (joinQueued s.queued)
          ((next, none), { s with
            queued := if rest.isEmpty then [] else [rest], queuedBytes := byteSize rest })
    if let some idle := idle then
      idle.resolve ()
    unless next.isEmpty do
      (← outbox.timer.get).watchdog.arm (.ofNat outbox.writeTimeout)
      outbox.write next

/--
Hands `buffer` to the outbox, which writes it after everything handed over before. Returns how many
bytes now wait behind the write in flight, or `none` if a write failed and `buffer` was dropped.
-/
def send [Transport α] (outbox : Outbox α) (buffer : ChunkedBuffer) : BaseIO (Option Nat) := do
  if buffer.size = 0 then
    return if (← outbox.state.get).failed then none else some 0
  let data := buffer.data
  let (now, rest) := split outbox.maxWriteBytes data
  let (start, queued?) ← outbox.state.modifyGet fun s =>
    if s.failed then ((false, none), s)
    else if s.writing then
      let queuedBytes := s.queuedBytes + buffer.size
      ((false, some queuedBytes), { s with queued := data :: s.queued, queuedBytes })
    else
      let queuedBytes := byteSize rest
      ((true, some queuedBytes), { s with
        writing := true, queued := if rest.isEmpty then [] else [rest], queuedBytes })
  if start then
    (← outbox.timer.get).watchdog.arm (.ofNat outbox.writeTimeout)
    outbox.write now
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
def lateSelector (outbox : Outbox α) : BaseIO (Selector Unit) :=
  return (← outbox.timer.get).ctx.doneSelector

/--
Waits until no write is in flight. If no write completes for `writeTimeout` milliseconds meanwhile,
the outbox fails instead, so a peer that stops reading cannot hold the connection. A write that ran
late but completed before this wait leaves the outbox working.
-/
partial def awaitIdle (outbox : Outbox α) : Async Unit := do
  let some idle ← outbox.idle? | return
  let timer ← outbox.timer.get
  if timer.stopped then return
  -- A completion replaces a fired timer, so a fired current one belongs to the write in flight.
  if ← timer.watchdog.hasFired then
    outbox.expire
    return
  let finished ← Selectable.one #[
    .case (taskSelector idle) (fun _ => pure true),
    .case timer.ctx.doneSelector (fun _ => pure false)]
  unless finished do
    outbox.awaitIdle

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
