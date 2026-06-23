/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Http.Data.Request
public import Std.Http.Data.Response
public import Std.Http.Data.Body.Any

public section

/-!
# Body.Empty

Represents an always-empty, already-closed body handle.
-/

namespace Std.Http.Body
open Std Async

set_option linter.all true

/--
An empty body handle.
-/
structure Empty where
deriving Inhabited, BEq

namespace Empty

/--
Receives from an empty body, always returning end-of-stream.
-/
@[inline]
def recv (_ : Empty) : Async (Option Chunk) :=
  pure none

/--
Closes an empty body (no-op).
-/
@[inline]
def close (_ : Empty) : Async Unit :=
  pure ()

/--
Empty bodies are always closed for reading.
-/
@[inline]
def isClosed (_ : Empty) : Async Bool :=
  pure true

/--
Non-blocking receive. Empty bodies are always at EOF.
-/
@[inline]
def tryRecv (_ : Empty) : Async (Option (Option Chunk)) :=
  pure (some none)

/--
Selector that immediately resolves with end-of-stream for an empty body.
-/
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

instance : Http.Body Empty where
  recv := Empty.recv
  close := Empty.close
  isClosed := Empty.isClosed
  recvSelector := Empty.recvSelector
  tryRecv := Empty.tryRecv
  getKnownSize _ := pure (some <| .fixed 0)
  setKnownSize _ _ := pure ()


instance : Coe Empty Any := ⟨Any.ofBody⟩

instance : Coe (Response Empty) (Response Any) where
  coe f := { f with }

instance : Coe (ContextAsync (Response Empty)) (ContextAsync (Response Any)) where
  coe action := do
    let response ← action
    pure (response : Response Any)

instance : Coe (Async (Response Empty)) (ContextAsync (Response Any)) where
  coe action := do
    let response ← action
    pure (response : Response Any)

end Body

namespace Request.Builder
open Async

/--
Builds a request with no body.
-/
def empty (builder : Builder) : Async (Request Body.Empty) :=
  pure <| builder.body {}

end Request.Builder

namespace Response.Builder
open Async

/--
Builds a response with no body.
-/
def empty (builder : Builder) : Async (Response Body.Empty) :=
  pure <| builder.body {}

end Response.Builder
