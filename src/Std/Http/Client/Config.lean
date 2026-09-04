/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Time
public import Std.Http.Protocol.H1
public import Std.Http.Client.Authenticator
public import Std.Http.Client.CookieHandler
public import Std.Http.Client.Proxy
public import Std.Http.Client.Error

public section

/-!
# Config

This module exposes the `Config` structure describing the timeouts, connection limits, and header
limits of an HTTP client, together with the per-request `RequestOverrides` that shadow it. The
policy hooks a `Config` points at live in their own modules: `Authenticator`, `CookieHandler`, and
`ProxySelector`.
-/

namespace Std.Http.Client

set_option linter.all true

/--
A strictly positive duration in milliseconds, used for client timeouts.
-/
abbrev Timeout := { x : Time.Millisecond.Offset // 0 < x }

/--
Per-request overrides for settings that otherwise come from the client-wide `Config`.
A `none` field defers to the configured value.

Every field must be handled in `apply`; one added here and forgotten there silently has no effect.
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
  Overrides `Config.onlySafeRedirects` for this request. Set this to opt a single unsafe request
  into (or out of) automatic redirect following without changing the client-wide policy.
  -/
  onlySafeRedirects : Option Bool := none

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
  How long a request carrying `Expect: 100-continue` waits for the interim response before sending
  its body anyway. RFC 9110 §10.1.1 requires a client not to wait indefinitely, since a server is
  free to ignore the expectation entirely.
  -/
  expectContinueTimeout : Timeout := ⟨1000, by decide⟩

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
  Chooses the proxy for each origin. When a request is routed through an HTTP proxy its URI is
  rewritten to absolute-form (`GET http://host/path HTTP/1.1`).
  Defaults to connecting every origin directly.
  -/
  proxySelector : ProxySelector := .direct

  /--
  Supplies credentials when a server answers `401` or a proxy answers `407`.
  `none` (default) reports those responses to the caller unanswered.
  -/
  authenticator : Option Authenticator := none

  /--
  Stores and replays cookies across requests.
  `none` (default) neither sends nor retains cookies.
  -/
  cookieHandler : Option CookieHandler := none

  /--
  Maximum number of bytes allowed in a single response body.
  When `some n`, reading more than `n` bytes from the body resolves the current
  request with an error and closes the connection.
  `none` (default) imposes no limit.
  -/
  maxResponseBodySize : Option Nat := none

  /--
  Maximum number of bytes read from the body of an intermediate response the client answers
  itself — a redirect it follows, or a challenge it authenticates — before the follow-up
  request is sent. A body larger than this is abandoned rather than read to its end.

  The bytes are held until the follow-up is known to have reached the peer, so an intermediate
  response the client turns out to be unable to answer can still be delivered whole. One abandoned
  for exceeding this limit cannot be, and the failure is reported instead.
  -/
  intermediateBodyDrainLimit : Nat := 1024 * 1024

namespace RequestOverrides

/--
Applies these overrides on top of `config`, producing the effective configuration for a single
request. Fields left `none` keep their configured value.
-/
def apply (overrides : RequestOverrides) (config : Config) : Config :=
  { config with
    requestTimeout := overrides.requestTimeout.getD config.requestTimeout
    maxRedirects := overrides.maxRedirects.getD config.maxRedirects
  }

end RequestOverrides

namespace Config

/--
Total header-block allowance implied by the client's own limits: `maxResponseHeaders` field lines,
each as long as `maxHeaderNameSize` and `maxHeaderValueSize` permit, plus the four bytes `": "` and
`CRLF` contribute per line. Deriving it keeps those three settings jointly reachable — the
machine's own aggregate default is smaller than they describe, so a response well inside all of
them would otherwise be rejected.
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
