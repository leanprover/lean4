/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Sync
public import Std.Internal.Async
public import Std.Internal.Http.Data.Request
public import Std.Internal.Http.Data.Response
public import Std.Internal.Http.Data.Body.Length
public import Std.Internal.Http.Data.Chunk
public import Init.Data.ByteArray

public section

/-!
# Body.Full

A body backed by a fixed `ByteArray` held in a `Mutex`.

The byte array is consumed at most once: the first call to `recv` or `tryRecv` atomically
takes the data and returns it as a single chunk; subsequent calls return `none` (end-of-stream).
Closing the body discards any unconsumed data.

`Full` implements `Body.Writer`. The `Writer` instance is a no-op for sends since the content is
fixed at construction; it is provided so that `Full` can substitute for a streaming channel in
contexts that require a writable body handle.
-/

namespace Std.Http.Body
open Std Internal IO Async

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

/--
Creates a `Full` body from a `ByteArray`.
-/
def ofByteArray (data : ByteArray) : Async Full := do
  let state ← Mutex.new (some data)
  return { state }

/--
Creates a `Full` body from a `String`.
-/
def ofUTF8String (data : String) : Async Full := do
  let state ← Mutex.new (some data.toUTF8)
  return { state }

/--
Atomically takes the byte array and returns it as a chunk.
Returns `none` if the data has already been consumed or the body is closed.
-/
def tryRecv (full : Full) : Async (Option Chunk) :=
  full.state.atomically do
    match ← get with
    | none => return none
    | some data =>
      set (none : Option ByteArray)
      if data.isEmpty then return none
      return some (Chunk.ofByteArray data)

/--
Receives the body data. Returns the full byte array on the first call as a single chunk,
then `none` on all subsequent calls.

The `count` hint is ignored; the entire content is always returned in one chunk.
-/
def recv (full : Full) (_count : Option UInt64) : Async (Option Chunk) :=
  full.tryRecv

/--
No-op send for a fixed full body.
-/
@[inline]
def send (_ : Full) (_ : Chunk) (_incomplete : Bool := false) : Async Unit :=
  pure ()

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
A fixed full body never has consumer interest.
-/
@[inline]
def hasInterest (_ : Full) : Async Bool :=
  pure false

/--
Returns known-size metadata based on current remaining bytes.
-/
def getKnownSize (full : Full) : Async (Option Body.Length) :=
  full.state.atomically do
    match ← get with
    | none => pure (some (.fixed 0))
    | some data => pure (some (.fixed data.size))

/--
No-op metadata setter for a fixed full body.
-/
@[inline]
def setKnownSize (_ : Full) (_ : Option Body.Length) : Async Unit :=
  pure ()

open Internal.IO.Async in
/--
Selector that immediately resolves to `false` for interest.
-/
def interestSelector (_ : Full) : Selector Bool where
  tryFn := pure (some false)
  registerFn waiter := do
    let lose := pure ()
    let win promise := do
      promise.resolve (.ok false)
    waiter.race lose win
  unregisterFn := pure ()

end Full

end Std.Http.Body

namespace Std.Http.Request.Builder
open Internal.IO.Async

private def fromBytesCore
    (builder : Builder)
    (content : ByteArray) :
    Async (Request Body.Full) := do
  return builder.body (← Body.Full.ofByteArray content)

/--
Builds a request from raw bytes.
-/
def fromBytes (builder : Builder) (content : ByteArray) : Async (Request Body.Full) :=
  fromBytesCore builder content

/--
Builds a request with a binary body.
-/
def bytes (builder : Builder) (content : ByteArray) : Async (Request Body.Full) := do
  let builder := builder.header Header.Name.contentType (Header.Value.ofString! "application/octet-stream")
  fromBytesCore builder content

/--
Builds a request with a text body.
-/
def text (builder : Builder) (content : String) : Async (Request Body.Full) := do
  let builder := builder.header Header.Name.contentType (Header.Value.ofString! "text/plain; charset=utf-8")
  fromBytesCore builder content.toUTF8

/--
Builds a request with a JSON body.
-/
def json (builder : Builder) (content : String) : Async (Request Body.Full) := do
  let builder := builder.header Header.Name.contentType (Header.Value.ofString! "application/json")
  fromBytesCore builder content.toUTF8

/--
Builds a request with an HTML body.
-/
def html (builder : Builder) (content : String) : Async (Request Body.Full) := do
  let builder := builder.header Header.Name.contentType (Header.Value.ofString! "text/html; charset=utf-8")
  fromBytesCore builder content.toUTF8

end Std.Http.Request.Builder

namespace Std.Http.Response.Builder
open Internal.IO.Async

private def fromBytesCore
    (builder : Builder)
    (content : ByteArray) :
    Async (Response Body.Full) := do
  return builder.body (← Body.Full.ofByteArray content)

/--
Builds a response from raw bytes.
-/
def fromBytes (builder : Builder) (content : ByteArray) : Async (Response Body.Full) :=
  fromBytesCore builder content

/--
Builds a response with a binary body.
-/
def bytes (builder : Builder) (content : ByteArray) : Async (Response Body.Full) := do
  let builder := builder.header Header.Name.contentType (Header.Value.ofString! "application/octet-stream")
  fromBytesCore builder content

/--
Builds a response with a text body.
-/
def text (builder : Builder) (content : String) : Async (Response Body.Full) := do
  let builder := builder.header Header.Name.contentType (Header.Value.ofString! "text/plain; charset=utf-8")
  fromBytesCore builder content.toUTF8

/--
Builds a response with a JSON body.
-/
def json (builder : Builder) (content : String) : Async (Response Body.Full) := do
  let builder := builder.header Header.Name.contentType (Header.Value.ofString! "application/json")
  fromBytesCore builder content.toUTF8

/--
Builds a response with an HTML body.
-/
def html (builder : Builder) (content : String) : Async (Response Body.Full) := do
  let builder := builder.header Header.Name.contentType (Header.Value.ofString! "text/html; charset=utf-8")
  fromBytesCore builder content.toUTF8

end Std.Http.Response.Builder
