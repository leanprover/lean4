/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Async
public import Std.Async.ContextAsync
public import Std.Http.Data.Chunk
public import Std.Http.Data.Headers
public import Std.Http.Data.Body.Length

public section

/-!
# Body.Basic

This module defines the `Body` typeclass for HTTP body streams, and shared conversion types
`ToByteArray` and `FromByteArray` used for encoding and decoding body content.
-/

namespace Std.Http
open Std Async

set_option linter.all true

/--
Typeclass for values that can be read as HTTP body streams.
-/
class Body (α : Type) where
  /--
  Receives the next body chunk. Returns `none` at end-of-stream.
  -/
  recv : α → Async (Option Chunk)

  /--
  Closes the body stream.
  -/
  close : α → Async Unit

  /--
  Returns `true` when the body stream is closed.
  -/
  isClosed : α → Async Bool

  /--
  Selector that resolves when a chunk is available or EOF is reached.
  -/
  recvSelector : α → Selector (Option Chunk)

  /--
  Non-blocking receive attempt. Returns `none` if no chunk is immediately available,
  `some (some chunk)` when a chunk is ready, or `some none` at end-of-stream.
  -/
  tryRecv (body : α) : Async (Option (Option Chunk))

  /--
  Gets the declared size of the body.
  -/
  getKnownSize : α → Async (Option Body.Length)

  /--
  Sets the declared size of a body.
  -/
  setKnownSize : α → Option Body.Length → Async Unit
end Std.Http

namespace Std.Http.Body

/--
Typeclass for types that can be converted to a `ByteArray`.
-/
class ToByteArray (α : Type) where

  /--
  Transforms into a `ByteArray`.
  -/
  toByteArray : α → ByteArray

instance : ToByteArray ByteArray where
  toByteArray := id

instance : ToByteArray String where
  toByteArray := String.toUTF8

/--
Typeclass for types that can be decoded from a `ByteArray`. The conversion may fail with an error
message if the bytes are not valid for the target type.
-/
class FromByteArray (α : Type) where

  /--
  Attempts to decode a `ByteArray` into the target type, returning an error message on failure.
  -/
  fromByteArray : ByteArray → Except String α

instance : FromByteArray ByteArray where
  fromByteArray := .ok

instance : FromByteArray String where
  fromByteArray bs :=
    match String.fromUTF8? bs with
    | some s => .ok s
    | none => .error "invalid UTF-8 encoding"

end Std.Http.Body
