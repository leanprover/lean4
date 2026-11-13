/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Http.Transport
public import Std.Http.Internal.ChunkedBuffer

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
  A write is in flight.
  -/
  writing : Bool := false

  /--
  The error of the write that failed, after which later output is dropped.
  -/
  error : Option IO.Error := none

  /--
  Resolved once no write is in flight.
  -/
  idle : Option (IO.Promise Unit) := none

  /--
  When a write last completed, by `IO.monoMsNow`; `0` before any did.
  -/
  completedAt : Nat := 0

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

  private state : IO.Ref Outbox.State

namespace Outbox

/--
Creates an outbox that writes to `socket`.
-/
def new (socket : α) : BaseIO (Outbox α) :=
  return { socket, state := ← IO.mkRef {} }

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
    let now ← IO.monoMsNow
    let (next, idle) ← outbox.state.modifyGet fun s =>
      match result with
      | .error err =>
        ((#[], s.idle), { s with queued := [], writing := false, error := some err, idle := none })
      | .ok () =>
        if s.queued.isEmpty then
          ((#[], s.idle), { s with writing := false, idle := none, completedAt := now })
        else ((joinQueued s.queued, none), { s with queued := [], completedAt := now })
    if let some idle := idle then
      idle.resolve ()
    unless next.isEmpty do
      outbox.write next

/--
Hands `buffer` to the outbox, which writes it after everything handed over before. Once a write
failed, `buffer` is dropped.
-/
def send [Transport α] (outbox : Outbox α) (buffer : ChunkedBuffer) : BaseIO Unit := do
  if buffer.size = 0 then
    return
  let data := buffer.data
  let start ← outbox.state.modifyGet fun s =>
    if s.error.isSome then (false, s)
    else if s.writing then (false, { s with queued := data :: s.queued })
    else (true, { s with writing := true })
  if start then
    outbox.write data

/--
A task that finishes once no write is in flight, or `none` if none is or a write failed.
-/
def idle? (outbox : Outbox α) : BaseIO (Option (Task (Option Unit))) := do
  let s ← outbox.state.get
  if !s.writing || s.error.isSome then
    return none
  if let some idle := s.idle then
    return some idle.result?
  let fresh ← IO.Promise.new
  outbox.state.modifyGet fun s =>
    if !s.writing || s.error.isSome then (none, s)
    else match s.idle with
      | some idle => (some idle.result?, s)
      | none => (some fresh.result?, { s with idle := some fresh })

/--
When a write last completed, by `IO.monoMsNow`; `0` before any did.
-/
def completedAt (outbox : Outbox α) : BaseIO Nat :=
  return (← outbox.state.get).completedAt

/--
The error of the write that failed, if one did.
-/
def error? (outbox : Outbox α) : BaseIO (Option IO.Error) :=
  return (← outbox.state.get).error

end Outbox

end Std.Http.Internal
