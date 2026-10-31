/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Async
public import Std.Http.Protocol.H1.Error

public section

/-!
# Client Errors

This module defines `Error`, the typed failure reported by every HTTP client operation, along with
the retry classification the client uses to decide whether a failed exchange may be replayed on a
fresh connection.
-/

namespace Std.Http.Client

open Std.Async

set_option linter.all true

/--
An error produced by the HTTP client. Connection-level failures (`connect`, `closed`, and a peer
that vanished mid-exchange) are eligible for automatic retry of idempotent requests; all other cases
are reported to the caller as-is.
-/
inductive Error where

  /--
  DNS resolution or transport connection establishment failed.
  -/
  | connect (message : String)

  /--
  The request exceeded its timeout.
  -/
  | timeout

  /--
  The connection was closed or shut down before the exchange completed.
  -/
  | closed (message : String)

  /--
  The peer violated the HTTP protocol.
  -/
  | protocol (error : Protocol.H1.Error)

  /--
  The response body exceeded `Config.maxResponseBodySize`.
  -/
  | bodyLimitExceeded

  /--
  The request could not be constructed (for example, the URL named no host).
  -/
  | invalidRequest (message : String)

  /--
  Any other I/O failure, e.g. raised by a middleware or a user-supplied body.
  -/
  | io (error : IO.Error)
deriving Inhabited

namespace Error

instance : ToString Error where
  toString
    | .connect msg => "connect: " ++ msg
    | .timeout => "request timeout"
    | .closed msg => msg
    | .protocol e => toString e
    | .bodyLimitExceeded => "response body exceeds maximum allowed size"
    | .invalidRequest msg => msg
    | .io e => toString e

/--
Renders this error as an `IO.Error` for callers working in `Async`.
-/
def toIOError (e : Error) : IO.Error :=
  .userError (toString e)

/--
Returns the success value, throwing the typed `Error` as an `IO.Error` otherwise. The `send` variant
at each client layer uses this to unwrap the result of the corresponding `trySend`.
-/
def throwOrPure {α : Type} : Except Error α → Async α
  | .ok a => pure a
  | .error e => throw e.toIOError

/--
`true` for connection-level failures that are safe to retry on a fresh connection (the request
provably produced no application-level effect, or the method is idempotent).
`Protocol.H1.Error.connectionClosed` is retryable: it is the stale keep-alive race, where the
server closed a pooled connection just as it was reused.
-/
def isRetryable : Error → Bool
  | .connect _ | .closed _ => true
  | .protocol e => e == Protocol.H1.Error.connectionClosed
  | .timeout | .bodyLimitExceeded | .invalidRequest _ | .io _ => false

end Error

end Std.Http.Client
