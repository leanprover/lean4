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
  Concrete body type produced by `onRequest`.
  Defaults to `Body.AnyBody`, but handlers may override it with any reader/writer-compatible body.
  -/
  ResponseBody : Type := Body.AnyBody

  /--
  Reader instance required by the connection loop for sending response chunks.
  -/
  [responseBodyReader : Body.Reader ResponseBody]

  /--
  Writer instance used for known-size metadata and protocol integration.
  -/
  [responseBodyWriter : Body.Writer ResponseBody]

  /--
  Called for each incoming HTTP request.
  -/
  onRequest (self : σ) (request : Request Body.Incoming) : ContextAsync (Response ResponseBody)

  /--
  Called when an error occurs while processing a request. The default implementation does nothing.
  -/
  onFailure (self : σ) (error : IO.Error) : Async Unit :=
    pure ()

  /--
  Called when a request includes an `Expect: 100-continue` header. Return `true` to send a
  `100 Continue` response and accept the body, or `false` to reject it. The default implementation
  always rejects.
  -/
  onContinue (self : σ) (request : Request.Head) : Async Bool :=
    pure false

end Std.Http.Server
