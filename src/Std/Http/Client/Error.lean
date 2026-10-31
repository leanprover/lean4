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
  The connection closed before the request was written to it: nothing reached the peer, so the
  request can be sent again whatever its method.
  -/
  | notSent (message : String)

  /--
  The peer violated the HTTP protocol.
  -/
  | protocol (error : Protocol.H1.Error)

  /--
  The response body exceeded `Config.maxResponseBodySize`, or the body of a challenge the client
  answers itself exceeded `Config.intermediateBodyDrainLimit`.
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
    | .notSent msg => msg
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
`true` for connection-level failures that a fresh connection may not repeat. Whether a request may
be sent again also depends on whether it could have reached the peer: see `isNeverSent`; anything
else is only safe to resend for an idempotent method. `Protocol.H1.Error.connectionClosed` is
retryable: it is the stale keep-alive race, where the server closed a pooled connection just as it
was reused.
-/
def isRetryable : Error → Bool
  | .connect _ | .closed _ | .notSent _ => true
  | .protocol e => e == Protocol.H1.Error.connectionClosed
  | .timeout | .bodyLimitExceeded | .invalidRequest _ | .io _ => false

/--
`true` for failures that prove the request never reached the peer: no connection could be opened, or
the one it was queued on closed before writing it.
-/
def isNeverSent : Error → Bool
  | .connect _ | .notSent _ => true
  | _ => false

end Error

end Std.Http.Client
