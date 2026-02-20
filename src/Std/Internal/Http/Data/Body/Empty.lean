/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Internal.Async
public import Std.Internal.Http.Data.Request
public import Std.Internal.Http.Data.Response
public import Std.Internal.Http.Data.Body.Length
public import Std.Internal.Http.Data.Body.Reader
public import Std.Internal.Http.Data.Chunk

public section

/-!
# Body.Empty

Represents an always-empty, already-closed body handle.
-/

namespace Std.Http.Body
open Std Internal IO Async

set_option linter.all true

/--
An empty body handle.
-/
structure Empty where
deriving Inhabited

namespace Empty

/-- Receives from an empty body, always returning end-of-stream. -/
@[inline]
def recv (_ : Empty) (_count : Option UInt64) : Async (Option Chunk) :=
  pure none

/-- Closes an empty body (no-op). -/
@[inline]
def close (_ : Empty) : Async Unit :=
  pure ()

/-- Empty bodies are always closed for reading. -/
@[inline]
def isClosed (_ : Empty) : Async Bool :=
  pure true

open Internal.IO.Async in
/-- Selector that immediately resolves with end-of-stream for an empty body. -/
@[inline]
def recvSelector (_ : Empty) : Selector (Option Chunk) where
  tryFn := pure (some none)
  registerFn waiter := do
    let lose := pure ()
    let win promise := do
      promise.resolve (.ok none)
    waiter.race lose win
  unregisterFn := pure ()

end Empty

instance : Reader Empty where
  recv := Empty.recv
  close := Empty.close
  isClosed := Empty.isClosed
  recvSelector := Empty.recvSelector

end Std.Http.Body

namespace Std.Http.Request.Builder
open Internal.IO.Async

/--
Builds a request with an empty body.
-/
def blank (builder : Builder) : Async (Request Body.Empty) :=
  pure <| builder.body {}

end Std.Http.Request.Builder

namespace Std.Http.Response.Builder
open Internal.IO.Async

/--
Builds a response with an empty body.
-/
def blank (builder : Builder) : Async (Response Body.Empty) :=
  pure <| builder.body {}

end Std.Http.Response.Builder
