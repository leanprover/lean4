/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Internal.Async.ContextAsync
public import Std.Internal.Http.Data.Headers
public import Std.Internal.Http.Data.Body.Length
public import Std.Internal.Http.Data.Body.ChunkStream
public import Std.Internal.Http.Data.Body.Full

public section

/-!
# Body

This module defines the `Body` typeclass, which provides a uniform interface for HTTP body types
including streaming and fully-buffered bodies.
-/

namespace Std.Http

set_option linter.all true

open Std Internal IO Async

/--
Typeclass that provides a uniform interface for HTTP body types. Implementations include
streaming bodies (`ByteStream`, `ChunkStream`) and fully-buffered bodies (`Full`).
-/
class Body (α : Type) (β : outParam Type) where
  /--
  Non-blocking receive. Returns `none` if the stream is closed or has ended,
  `some` if data is available.
  -/
  recv? : α → Async (Option β)

  /--
  Blocking receive. Blocks if no data is available yet. Returns `none` if the stream
  is closed or has ended, `some` if data becomes available. If an amount is specified,
  accumulates bytes up to that size before returning.
  -/
  recv : α → Option UInt64 → Async (Option β)

  /--
  Send data to the body. May block if the buffer is full.
  -/
  send : α → β → Async Unit

  /--
  Checks if the body is closed.
  -/
  isClosed : α → Async Bool

  /--
  Returns the known size of the body if available.
  -/
  size? : α → Async (Option Body.Length)

  /--
  Creates an empty body.
  -/
  empty : Async α

  /--
  Creates a `Selector` for multiplexing receive operations. Resolves once data is available
  and provides it, or returns `none` when the body is closed.
  -/
  recvSelector : α → Selector (Option β)

instance : Body Body.ChunkStream Chunk where
  recv? := Body.ChunkStream.tryRecv
  recv := Body.ChunkStream.recv
  send := Body.ChunkStream.send
  isClosed := Body.ChunkStream.isClosed
  size? := Body.ChunkStream.getKnownSize
  empty := Body.ChunkStream.empty
  recvSelector := Body.ChunkStream.recvSelector

instance : Body Body.Full Chunk where
  recv? full := do return (← Body.Full.recv? full).map Chunk.ofByteArray
  recv full count := do return (← Body.Full.recv full count).map Chunk.ofByteArray
  send full chunk := Body.Full.send full chunk.data
  isClosed := Body.Full.isClosed
  size? := Body.Full.size?
  empty := Body.Full.empty
  recvSelector := Body.Full.recvSelector

end Std.Http
