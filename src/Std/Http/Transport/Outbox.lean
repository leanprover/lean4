/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Http.Transport

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
  Output handed over while a write was in flight, written together once it completes.
  -/
  queued : Array ByteArray := #[]

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
Writes a connection's output to `socket` in order without the connection waiting for it. Output
handed over while a write is in flight goes out in a single write once that write completes, started
by the thread that completed it. A connection thus keeps producing output while its earlier output
is written, and another thread can add output after it.
-/
structure Outbox (α : Type) where
  private mk ::

  /--
  The transport the output is written to.
  -/
  socket : α

  private state : IO.Ref Outbox.State

namespace Outbox

/--
Creates an outbox that writes to `socket`.
-/
def new (socket : α) : BaseIO (Outbox α) :=
  return { socket, state := ← IO.mkRef {} }

/--
Starts writing `data`, then whatever was queued meanwhile once the write completes. For a socket,
the next write thus starts on the event loop's own thread, which does not have to wait for it.
-/
private partial def write [Transport α] (outbox : Outbox α) (data : Array ByteArray) :
    BaseIO Unit := do
  let task ← EAsync.toBaseIO (Transport.sendAll outbox.socket data)
  BaseIO.chainTask (sync := true) task fun result => do
    let (next, idle) ← outbox.state.modifyGet fun s =>
      match result with
      | .error err =>
        ((#[], s.idle), { s with
          queued := #[], queuedBytes := 0, writing := false, failed := true, error := some err
          idle := none })
      | .ok () =>
        if s.queued.isEmpty then ((#[], s.idle), { s with writing := false, idle := none })
        else ((s.queued, none), { s with queued := #[], queuedBytes := 0 })
    if let some idle := idle then
      idle.resolve ()
    unless next.isEmpty do
      outbox.write next

/--
Hands `buffer` to the outbox, which writes it after everything handed over before. Returns how many
bytes now wait behind the write in flight, or `none` if a write failed and `buffer` was dropped.
-/
def send [Transport α] (outbox : Outbox α) (buffer : ChunkedBuffer) : BaseIO (Option Nat) := do
  if buffer.size = 0 then
    return some 0
  let data := buffer.data
  let (start, queued?) ← outbox.state.modifyGet fun s =>
    if s.failed then ((false, none), s)
    else if s.writing then
      let queuedBytes := s.queuedBytes + buffer.size
      ((false, some queuedBytes), { s with queued := s.queued ++ data, queuedBytes })
    else ((true, some 0), { s with writing := true })
  if start then
    outbox.write data
  return queued?

/--
A task that finishes once no write is in flight, or `none` if none is.
-/
def idle? (outbox : Outbox α) : BaseIO (Option (Task (Option Unit))) := do
  unless (← outbox.state.get).writing do
    return none
  let fresh ← IO.Promise.new
  outbox.state.modifyGet fun s =>
    if !s.writing then (none, s)
    else match s.idle with
      | some idle => (some idle.result?, s)
      | none => (some fresh.result?, { s with idle := some fresh })

/--
Waits until no write is in flight.
-/
def awaitIdle (outbox : Outbox α) : Async Unit := do
  if let some idle ← outbox.idle? then
    BaseAsync.ofTask (Task.map (sync := true) (fun _ => (Except.ok () : Except IO.Error Unit)) idle)

/--
Returns `true` once a write failed.
-/
def failed (outbox : Outbox α) : BaseIO Bool :=
  return (← outbox.state.get).failed

/--
Takes the error of the failed write, so that only the first caller gets it.
-/
def takeError? (outbox : Outbox α) : BaseIO (Option IO.Error) :=
  outbox.state.modifyGet fun s => (s.error, { s with error := none })

/--
Hands `buffer` to the outbox, then waits for its writes if more than `limit` bytes are queued, so a
peer that does not read holds up the caller instead of growing its memory. Returns `false` if a
write failed.
-/
def push [Transport α] (outbox : Outbox α) (buffer : ChunkedBuffer) (limit : Nat := 65536) :
    Async Bool := do
  match ← outbox.send buffer with
  | some queued =>
    if queued < limit then
      return true
    outbox.awaitIdle
    return !(← outbox.failed)
  | none => return false

end Outbox

end Std.Http.Internal
