/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Internal.Async
public import Std.Internal.Http.Data
public import Std.Internal.Async.ContextAsync

public section

namespace Std.Http.Server

open Std.Internal.IO.Async

set_option linter.all true

/--
A type class for handling HTTP server events. Implement this class to define how the server
responds to incoming requests, failures, and `Expect: 100-continue` headers.
-/
class Handler (σ : Type) where
  /--
  Called for each incoming HTTP request. The default implementation returns a 404 Not Found response.
  -/
  onRequest (self : σ) (request : Request Body.Incoming) : ContextAsync (Response Body.Outgoing) := do
    let (body, _incoming) ← Body.mkChannel
    body.setKnownSize (some (.fixed 0))
    body.close
    pure { head := { status := .notFound }, body }

  /--
  Called when an error occurs while processing a request. The default implementation does nothing.
  -/
  onFailure (self : σ) (error : IO.Error) : Async Unit :=
    pure ()

  /--
  Called when a request includes an `Expect: 100-continue` header. Return `true` to send a
  `100 Continue` response and accept the body, or `false` to reject it. The default implementation
  always accepts.
  -/
  onContinue (self : σ) (request : Request.Head) : Async Bool :=
    pure true

end Std.Http.Server
