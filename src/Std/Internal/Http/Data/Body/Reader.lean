/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Internal.Async
public import Std.Internal.Http.Data.Chunk
public import Std.Internal.Http.Data.Body.Basic
public import Std.Internal.Http.Data.Body.Stream

public section

/-!
# Body.Reader

Reader typeclass for body-like values that can be consumed as chunk streams.
-/

namespace Std.Http.Body
open Std Internal IO Async

set_option linter.all true

/--
Typeclass for values that can be read as HTTP body streams.
-/
class Reader (α : Type) where
  /--
  Receives the next body chunk. Returns `none` at end-of-stream.
  -/
  recv : α → Option UInt64 → Async (Option Chunk)

  /--
  Closes the reader stream.
  -/
  close : α → Async Unit

  /--
  Returns `true` when the reader stream is closed.
  -/
  isClosed : α → Async Bool

  /--
  Selector that resolves when a chunk is available or EOF is reached.
  -/
  recvSelector : α → Selector (Option Chunk)

instance : Reader Incoming where
  recv := Incoming.recv
  close := Incoming.close
  isClosed := Incoming.isClosed
  recvSelector := Incoming.recvSelector

end Std.Http.Body
