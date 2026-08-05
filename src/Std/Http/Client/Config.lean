/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Time
public import Std.Http.Protocol.H1

public section

/-!
# Config

This module exposes the `Config` structure describing timeouts, connection,
and header configurations for an HTTP client, the typed `Error` reported by
client operations, and per-request `RequestOverrides`.
-/

namespace Std.Http.Client

set_option linter.all true

/--
A strictly positive duration in milliseconds, used for client timeouts.
-/
abbrev Timeout := { x : Time.Millisecond.Offset // 0 < x }

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
def throwOrPure {α : Type} : Except Error α → Std.Async.Async α
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

/--
Per-request overrides for settings that otherwise come from the client-wide `Config`.
A `none` field defers to the configured value.
-/
structure RequestOverrides where

  /--
  Overrides `Config.requestTimeout` for this request.
  -/
  requestTimeout : Option Timeout := none

  /--
  Overrides `Config.maxRedirects` for this request. `some 0` disables redirect following.
  -/
  maxRedirects : Option Nat := none

/--
Client connection configuration.
-/
structure Config where
  /--
  Maximum number of requests per connection (for keep-alive).
  -/
  maxRequestsPerConnection : Nat := 1000

  /--
  Maximum number of headers allowed per response.
  -/
  maxResponseHeaders : Nat := 200

  /--
  Maximum size of a single header name in bytes.
  -/
  maxHeaderNameSize : Nat := 256

  /--
  Maximum size of a single header value in bytes.
  -/
  maxHeaderValueSize : Nat := 16384

  /--
  Maximum time to wait for the next chunk of data on an open connection before declaring it stale.
  This is a per-read idle timeout, not a wall-clock limit on the total request duration; use
  `requestTimeout` to bound the full exchange.
  -/
  readTimeout : Timeout := ⟨30000, by decide⟩

  /--
  How long an idle connection may sit in the pool before it is closed. Only relevant when
  `enableKeepAlive` is `true`. This is distinct from `readTimeout`: `readTimeout` fires mid-read;
  `keepAliveTimeout` fires while the connection is parked waiting for the next request.
  -/
  keepAliveTimeout : Timeout := ⟨4000, by decide⟩

  /--
  Timeout for the request lifecycle (send + receive) per connection.
  DNS resolution and TCP connect are not covered by this timeout; see `connectTimeout`.
  -/
  requestTimeout : Timeout := ⟨120000, by decide⟩

  /--
  Timeout for establishing a new connection, covering DNS resolution and the transport
  connect. Complements `requestTimeout`, which starts only once a connection exists.
  -/
  connectTimeout : Timeout := ⟨30000, by decide⟩

  /--
  Whether to enable keep-alive connections.
  -/
  enableKeepAlive : Bool := true

  /--
  Maximum number of bytes to receive in a single read call.
  -/
  maxRecvChunkSize : Nat := 16384

  /--
  Default buffer size for request payloads.
  -/
  defaultRequestBufferSize : Nat := 16384

  /--
  The user-agent string to send by default.
  -/
  userAgent : Option Header.Value := some (.mk "lean-http/1.1")

  /--
  Maximum number of redirects to follow automatically.
  Set to `0` to disable automatic redirect following.
  -/
  maxRedirects : Nat := 10

  /--
  When `true`, automatic redirect following is restricted to requests whose
  original method is safe (RFC 9110 §9.2.1: GET, HEAD, OPTIONS, TRACE).
  Redirects for unsafe methods (POST, PUT, DELETE, PATCH, …) are not followed
  automatically — the response is returned as-is for the caller to handle.

  Defaults to `false` so that the standard 301/302 POST→GET downgrade and
  307/308 method-preserving redirects work out of the box.
  -/
  onlySafeRedirects : Bool := false

  /--
  Optional HTTP proxy address as `(host, port)`.
  When set, all TCP connections are routed through this proxy and
  request URIs are rewritten to absolute-form (`GET http://host/path HTTP/1.1`).
  -/
  proxy : Option (String × UInt16) := none

  /--
  Maximum number of bytes allowed in a single response body.
  When `some n`, reading more than `n` bytes from the body resolves the current
  request with an error and closes the connection.
  `none` (default) imposes no limit.
  -/
  maxResponseBodySize : Option Nat := none

  /--
  Maximum number of bytes drained from an intermediate redirect response body
  before the redirected request is sent.
  -/
  redirectBodyDrainLimit : Nat := 1024 * 1024

namespace Config

/--
Total header-block allowance implied by the client's own limits: `maxResponseHeaders` field lines,
each as long as `maxHeaderNameSize` and `maxHeaderValueSize` permit, plus the four bytes `": "` and
`CRLF` contribute per line. Deriving it keeps those three settings jointly reachable — the machine's
own aggregate default is smaller than they describe, so a response well inside all of them would
otherwise be rejected.
-/
def headerBlockSize (config : Config) : Nat :=
  config.maxResponseHeaders * (config.maxHeaderNameSize + config.maxHeaderValueSize + 4)

/--
Converts to HTTP/1.1 protocol configuration.
-/
def toH1Config (config : Config) : Std.Http.Protocol.H1.Config where
  maxMessages := config.maxRequestsPerConnection
  maxHeaders := config.maxResponseHeaders
  maxHeaderNameLength := config.maxHeaderNameSize
  maxHeaderValueLength := config.maxHeaderValueSize
  maxHeaderBytes := config.headerBlockSize
  enableKeepAlive := config.enableKeepAlive
  agentName := config.userAgent
  maxBodySize := 2 ^ 64
  maxChunkSize := 2 ^ 64
  maxBufferedBodyBytes := some (64 * 1024 * 1024)

end Std.Http.Client.Config
