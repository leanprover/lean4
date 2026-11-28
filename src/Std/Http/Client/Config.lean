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
public import Std.Http.Client.Interceptor

public section

/-!
# Config

This module exposes the `Config` structure describing the timeouts, connection limits, and header
limits of an HTTP client, together with the per-request `RequestOverrides` that shadow it. The
policy hooks a `Config` points at live in their own modules: `Authenticator`, `CookieHandler`,
`Interceptor`, and `ProxySelector`.
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
  Overrides `Config.responseTimeout` for this request.
  -/
  responseTimeout : Option Timeout := none

  /--
  Overrides `Config.maxRedirects` for this request. `some 0` disables redirect following.
  -/
  maxRedirects : Option Nat := none

/--
Decides whether the client follows a redirect it would otherwise follow, given the origin and the
request of the hop that was redirected, the redirect's status, and the plan for the next hop.
-/
abbrev RedirectPolicy := URI.Origin → Request.Head → Status → Protocol.H1.RedirectPlan → Bool

/--
Client connection configuration.
-/
structure Config where
  /--
  Maximum number of requests per connection (for keep-alive).
  -/
  maxRequests : Nat := 1000

  /--
  Maximum number of headers allowed per response.
  -/
  maxHeaders : Nat := 200

  /--
  Maximum size of a single header name in bytes.
  -/
  maxHeaderNameLength : Nat := 256

  /--
  Maximum size of a single header value in bytes.
  -/
  maxHeaderValueLength : Nat := 16384

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
  Bounds each pause in an exchange on a connection: in sending the request, in waiting for the response
  head, and in the response body, whether the peer stops or the caller stops reading. An upload or a
  download of any length goes through for as long as it keeps moving.
  Each redirect hop and authentication retry is a new exchange with a bound of its own. DNS
  resolution and the transport connect are covered by `connectTimeout` instead.
  -/
  requestTimeout : Timeout := ⟨120000, by decide⟩

  /--
  Bounds the whole wait for a response, from sending the request to the response head reaching the
  caller: waiting for a connection, connecting, sending the request and its body, redirects, retries
  and authentication. A request still unanswered when it passes fails with `Error.timeout`. Reading
  the response body is not covered; `requestTimeout` bounds each pause there. Raise it for request
  bodies that take longer than this to send.
  -/
  responseTimeout : Timeout := ⟨300000, by decide⟩

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
  maximumRecvSize : Nat := 16384

  /--
  Default buffer size for request payloads.
  -/
  defaultPayloadBytes : Nat := 16384

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
  Decides which redirects are followed, of those the client would follow (RFC 9110 §15.4, within
  `maxRedirects`). `none` (default) follows them all.
  -/
  redirectPolicy : Option RedirectPolicy := none

  /--
  Statuses of final responses the client sends the request again for, like a connection-level
  failure: only when the request can be sent again whole (an idempotent method and a body that
  rewinds), and within the retries the client allows. The response body is read and discarded
  first, within `intermediateBodyDrainLimit`. Empty by default; `429 Too Many Requests` and
  `503 Service Unavailable` are the usual choices.
  -/
  retryStatuses : Array Status := #[]

  /--
  The delay before the first retry, doubled for each further one up to `maxRetryDelay`, whether the
  retry follows a connection-level failure or a status in `retryStatuses`. A response's
  `Retry-After` given in seconds sets the delay instead. `0` (default) retries at once.
  -/
  retryDelay : Time.Millisecond.Offset := 0

  /--
  The longest delay before a retry, whatever the doubling or a `Retry-After` asks for.
  -/
  maxRetryDelay : Time.Millisecond.Offset := 30000

  /--
  Hooks run around each hop: before it is sent, and when its response heads arrive.
  `none` (default) runs none.
  -/
  interceptor : Option Interceptor := none

  /--
  Maximum number of connections a client keeps open to one origin at a time, counting those still
  being opened. HTTP/1.1 carries one exchange per connection at a time, so this is also how many
  requests to one origin run concurrently; a request that finds them all busy waits for the next one
  to come free.
  -/
  maxConnectionsPerOrigin : { n : Nat // 0 < n } := ⟨8, by decide⟩

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
  Maximum number of response bytes the connection holds that the caller has not yet read. The
  connection stops reading from the socket well before this, while the caller has body bytes in hand,
  so the limit is only reached by a peer that sends more than one read asks for; past it the response
  fails as too large.
  -/
  maxBufferedBodyBytes : Nat := 64 * 1024 * 1024

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
    responseTimeout := overrides.responseTimeout.getD config.responseTimeout
    maxRedirects := overrides.maxRedirects.getD config.maxRedirects
  }

end RequestOverrides

namespace Config

/--
Total header-block allowance implied by the client's own limits: `maxHeaders` field lines, each as
long as `maxHeaderNameLength` and `maxHeaderValueLength` permit, plus the four bytes `": "` and
`CRLF` contribute per line. Deriving it keeps those three settings jointly reachable — the
machine's own aggregate default is smaller than they describe, so a response well inside all of
them would otherwise be rejected.
-/
def headerBlockSize (config : Config) : Nat :=
  config.maxHeaders * (config.maxHeaderNameLength + config.maxHeaderValueLength + 4)

/--
Converts to HTTP/1.1 protocol configuration.
-/
def toH1Config (config : Config) : Std.Http.Protocol.H1.Config where
  maxMessages := config.maxRequests
  maxHeaders := config.maxHeaders
  maxHeaderNameLength := config.maxHeaderNameLength
  maxHeaderValueLength := config.maxHeaderValueLength
  maxHeaderBytes := config.headerBlockSize
  enableKeepAlive := config.enableKeepAlive
  agentName := config.userAgent
  maxBodySize := 2 ^ 64
  maxChunkSize := 2 ^ 64
  maxBufferedBodyBytes := some config.maxBufferedBodyBytes

end Std.Http.Client.Config
