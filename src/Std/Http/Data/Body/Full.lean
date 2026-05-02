/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Sync
public import Std.Http.Data.Request
public import Std.Http.Data.Response
public import Std.Http.Data.Body.Any
public import Init.Data.ByteArray

public section

/-!
# Body.Full

A body backed by a fixed `ByteArray` held in a `Mutex`.

The byte array is consumed at most once: the first call to `recv` atomically takes the data
and returns it as a single chunk; subsequent calls return `none` (end-of-stream).
Closing the body discards any unconsumed data.
-/

namespace Std.Http.Body
open Std Async

set_option linter.all true

/--
A body backed by a fixed, mutex-protected `ByteArray`.

The data is consumed on the first read. Once consumed (or explicitly closed), the body
behaves as a closed, empty channel.
-/
structure Full where
  private mk ::
  private state : Mutex (Option ByteArray)
deriving Nonempty

namespace Full

private def takeChunk : AtomicT (Option ByteArray) Async (Option Chunk) := do
  match ← get with
  | none =>
    pure none
  | some data =>
    set (none : Option ByteArray)
    if data.isEmpty then
      pure none
    else
      pure (some (Chunk.ofByteArray data))

/--
Creates a `Full` body from a `ByteArray`.
-/
def ofByteArray (data : ByteArray) : Async Full := do
  let state ← Mutex.new (some data)
  return { state }

/--
Creates a `Full` body from a `String`.
-/
def ofString (data : String) : Async Full := do
  let state ← Mutex.new (some data.toUTF8)
  return { state }

/--
Receives the body data. Returns the full byte array on the first call as a single chunk,
then `none` on all subsequent calls.
-/
def recv (full : Full) : Async (Option Chunk) :=
  full.state.atomically do
    takeChunk

/--
Closes the body, discarding any unconsumed data.
-/
def close (full : Full) : Async Unit :=
  full.state.atomically do
    set (none : Option ByteArray)

/--
Returns `true` when the data has been consumed or the body has been closed.
-/
def isClosed (full : Full) : Async Bool :=
  full.state.atomically do
    return (← get).isNone

/--
Returns the known size of the remaining data.
Returns `some (.fixed n)` with the current byte count, or `some (.fixed 0)` if the body has
already been consumed or closed.
-/
def getKnownSize (full : Full) : Async (Option Body.Length) :=
  full.state.atomically do
    match ← get with
    | none => pure (some (.fixed 0))
    | some data => pure (some (.fixed data.size))

/--
Non-blocking receive. `Full` bodies are always in-memory, so data is always
immediately available. Returns `some chunk` on first call, `some none` (EOF)
once consumed or closed.
-/
def tryRecv (full : Full) : Async (Option (Option Chunk)) := do
  return some (← full.state.atomically takeChunk)

/--
Selector that immediately resolves to the remaining chunk (or EOF).
-/
def recvSelector (full : Full) : Selector (Option Chunk) where
  tryFn := do
    let chunk ← full.state.atomically do
      takeChunk
    pure (some chunk)

  registerFn waiter := do
    full.state.atomically do
      let lose := pure ()

      let win promise := do
        let chunk ← takeChunk
        promise.resolve (.ok chunk)

      waiter.race lose win

  unregisterFn := pure ()

end Full

instance : Http.Body Full where
  recv := Full.recv
  close := Full.close
  isClosed := Full.isClosed
  recvSelector := Full.recvSelector
  tryRecv := Full.tryRecv
  getKnownSize := Full.getKnownSize
  setKnownSize _ _ := pure ()

instance : Coe Full Any := ⟨Any.ofBody⟩

instance : Coe (Response Full) (Response Any) where
  coe f := { f with }

instance : Coe (ContextAsync (Response Full)) (ContextAsync (Response Any)) where
  coe action := do
    let response ← action
    pure (response : Response Any)

instance : Coe (Async (Response Full)) (ContextAsync (Response Any)) where
  coe action := do
    let response ← action
    pure (response : Response Any)

end Body

namespace Request.Builder

open Async

/--
Builds a request body from raw bytes without setting any headers.
Use `bytes` instead if you want `Content-Type: application/octet-stream` set automatically.
-/
def fromBytes (builder : Builder) (content : ByteArray) : Async (Request Body.Full) := do
  return builder.body (← Body.Full.ofByteArray content)

/--
Builds a request with a binary body.
Sets `Content-Type: application/octet-stream`.
Use `fromBytes` instead if you need to set a different `Content-Type` or none at all.
-/
def bytes (builder : Builder) (content : ByteArray) : Async (Request Body.Full) :=
  fromBytes (builder.header Header.Name.contentType (Header.Value.ofString! "application/octet-stream")) content

/--
Builds a request with a text body.
Sets `Content-Type: text/plain; charset=utf-8`.
-/
def text (builder : Builder) (content : String) : Async (Request Body.Full) :=
  fromBytes (builder.header Header.Name.contentType (Header.Value.ofString! "text/plain; charset=utf-8")) content.toUTF8

/--
Builds a request with a JSON body.
Sets `Content-Type: application/json`.
-/
def json (builder : Builder) (content : String) : Async (Request Body.Full) :=
  fromBytes (builder.header Header.Name.contentType (Header.Value.ofString! "application/json")) content.toUTF8

/--
Builds a request with an HTML body.
Sets `Content-Type: text/html; charset=utf-8`.
-/
def html (builder : Builder) (content : String) : Async (Request Body.Full) :=
  fromBytes (builder.header Header.Name.contentType (Header.Value.ofString! "text/html; charset=utf-8")) content.toUTF8

end Request.Builder

namespace Response.Builder
open Async

/--
Builds a response body from raw bytes without setting any headers.
Use `bytes` instead if you want `Content-Type: application/octet-stream` set automatically.
-/
def fromBytes (builder : Builder) (content : ByteArray) : Async (Response Body.Full) := do
  return builder.body (← Body.Full.ofByteArray content)

/--
Builds a response with a binary body.
Sets `Content-Type: application/octet-stream`.
Use `fromBytes` instead if you need to set a different `Content-Type` or none at all.
-/
def bytes (builder : Builder) (content : ByteArray) : Async (Response Body.Full) :=
  fromBytes (builder.header Header.Name.contentType (Header.Value.ofString! "application/octet-stream")) content

/--
Builds a response with a text body.
Sets `Content-Type: text/plain; charset=utf-8`.
-/
def text (builder : Builder) (content : String) : Async (Response Body.Full) :=
  fromBytes (builder.header Header.Name.contentType (Header.Value.ofString! "text/plain; charset=utf-8")) content.toUTF8

/--
Builds a response with a JSON body.
Sets `Content-Type: application/json`.
-/
def json (builder : Builder) (content : String) : Async (Response Body.Full) :=
  fromBytes (builder.header Header.Name.contentType (Header.Value.ofString! "application/json")) content.toUTF8

/--
Builds a response with an HTML body.
Sets `Content-Type: text/html; charset=utf-8`.
-/
def html (builder : Builder) (content : String) : Async (Response Body.Full) :=
  fromBytes (builder.header Header.Name.contentType (Header.Value.ofString! "text/html; charset=utf-8")) content.toUTF8

end Response.Builder
