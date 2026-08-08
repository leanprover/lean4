/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Http.Client.Connection
public import Std.Http.Client.Connector
public import Std.Http.Protocol.H1.Redirect
import Init.Data.Array

public section

/-!
# Client

An HTTP/1.1 client that opens connections, reuses them across requests, follows redirects, and
retries connection-level failures.

The client keeps at most one reusable connection. If the next request targets that connection's
origin, the connection is reused; if the origin changes, the current connection is retired and a
new one is opened. Transport establishment is delegated to a `Connector`, so plain TCP, TLS, and
mock transports all plug in the same way.

Use `Client.new` to create a client, then `client.send` to dispatch requests.
-/

set_option linter.all true

namespace Std.Http.Client

open Std Async TCP Protocol H1
open Time

/--
A middleware intercepts every request/response hop performed by a `Client`.

The function receives the outgoing request and a `next` continuation that performs
the actual send. Call `next req` to forward the (possibly modified) request downstream;
the result carries either the response or the typed `Error` that ended the hop, which
the middleware may inspect, replace, or recover from. Return `.ok response` without
calling `next` to short-circuit the chain.

Middlewares are composed outermost-first: the first element in the array wraps all
subsequent ones. Each middleware must call `next` at most once per invocation.
-/
abbrev Middleware :=
  Request Body.Any → (Request Body.Any → Async (Except Error (Response Body.Stream))) →
    Async (Except Error (Response Body.Stream))

/--
The single reusable connection currently held by a client.
-/
structure Slot where
  /--
  Origin this connection is connected to.
  -/
  origin : URI.Origin

  /--
  The current connection.
  -/
  connection : Connection

end Std.Http.Client

namespace Std.Http

open Std Async

/--
An HTTP client: a reusable connection, the configuration used to open new ones, and the
redirect/retry policy applied to every request.
-/
structure Client where
  /--
  Current reusable connection, if any.
  -/
  state : Mutex (Option Client.Slot)

  /--
  Configuration used when creating new connections.
  -/
  config : Client.Config

  /--
  Monotonically increasing counter for unique connection IDs.
  -/
  nextId : Mutex UInt64

  /--
  Middlewares applied (outermost-first) around every request/response hop.
  -/
  middlewares : Array Client.Middleware := #[]

  /--
  Function used to open new transport connections. Supply a custom `Connector` via `Client.new`.
  -/
  connect : Client.Connector := Client.Connector.tcp

  /--
  Maximum number of times to retry a failed request on a fresh connection. `0` disables
  retries.

  Retries only apply to connection-level failures (the connection died before a response was
  received). Application-level errors (4xx, 5xx) are never retried automatically.

  **Only idempotent methods with replayable bodies are retried.** Requests whose method
  returns `false` from `Method.isIdempotent` (e.g. `POST`, `PATCH`) are never retried
  regardless of this value, to prevent unintended duplicate side-effects.
  -/
  maxRetries : Nat := 1

namespace Client

open Std Async TCP Protocol H1
open Time

/--
Creates a new client with no open connection. Supply a custom `connect` function (e.g. a TLS
connector or a mock) to customize how transport connections are opened.
-/
def new (config : Config := {}) (connect : Connector := Connector.tcp)
    (maxRetries : Nat := defaultMaxRetries) (middlewares : Array Middleware := #[]) :
    Async Client := do
  let state ← Mutex.new (none : Option Slot)
  let nextId ← Mutex.new (1 : UInt64)
  pure { state, config, nextId, middlewares, connect, maxRetries }

/--
Closes and removes the client's current connection, if any. The client remains usable: a later
`send` simply opens a fresh connection.
-/
def close (client : Client) : Async Unit := do
  let slot ← client.state.atomically <| modifyGet fun slot => (slot, none)
  if let some slot := slot then
    slot.connection.close

/--
Acquires a fresh unique connection ID.
-/
private def nextConnectionId (client : Client) : Async UInt64 :=
  client.nextId.atomically <| modifyGet fun id => (id, id + 1)

/--
Opens a new connection for `origin` and assigns it a client-local ID. The connector runs under
`Config.connectTimeout`, bounding DNS resolution and the transport connect. An exception
thrown by a custom connector is reported as `Error.connect`, keeping every connector-level
failure typed on one path.
-/
private def openConnection (client : Client) (origin : URI.Origin) :
    Async (Except Error Connection) := do
  let resultChannel : Std.Channel (Except Error Connection) ← Std.Channel.new

  let connectTask ← async (t := AsyncTask) do
    try
      client.connect origin.scheme origin.host origin.port client.config
    catch err =>
      pure (.error (.connect (toString err)))

  BaseIO.chainTask connectTask fun
    | .ok result => discard <| resultChannel.send result
    | .error err => discard <| resultChannel.send (.error (.connect (toString err)))

  let outcome ← Selectable.one #[
    .case resultChannel.recvSelector (fun result => pure (some result)),
    .case (← Selector.sleep client.config.connectTimeout.val) (fun _ => pure none)
  ]

  match outcome with
  | some (.ok connection) =>
    let id ← nextConnectionId client
    return .ok { connection with id }
  | some (.error e) => return .error e
  | none =>
    -- The connector may still complete after the timeout; drain its result in the
    -- background and close the late connection so the transport does not leak.
    background do
      let late ← Selectable.one #[.case resultChannel.recvSelector pure]
      if let .ok connection := late then
        connection.close
    let timeout := client.config.connectTimeout.val
    return .error (.connect
      s!"connecting to {origin.host}:{origin.port} timed out after {timeout}ms")

/--
Returns the client's connection for `origin`.

If the current connection has the same origin, it is checked out again; HTTP/1.1 requests
queue on the connection. If the origin differs, the current connection is retired and replaced.

A new connection is opened *outside* the state mutex: DNS resolution and the TCP connect can block,
and holding the lock across them would serialize every other operation (including connection
retirement). The lock is taken only for the brief fast-path check and to install the freshly
opened connection.
-/
def getOrCreateConnection (client : Client) (origin : URI.Origin) :
    Async (Except Error Connection) := do
  let existing ← client.state.atomically do
    match ← get with
    | some slot =>
      if slot.origin == origin then
        if ← slot.connection.isClosed then
          set (none : Option Slot)
          pure none
        else
          pure (some slot.connection)
      else
        pure none
    | none => pure none
  if let some connection := existing then
    return .ok connection

  match ← client.openConnection origin with
  | .error e => return .error e
  | .ok connection =>
    let (chosen, evicted) ← client.state.atomically do
      match ← get with
      | some slot =>
        if slot.origin == origin then
          pure (slot.connection, some connection)
        else
          set (some ({ origin, connection } : Slot))
          pure (connection, some slot.connection)
      | none =>
        set (some ({ origin, connection } : Slot))
        pure (connection, none)

    if let some evictedConnection := evicted then
      evictedConnection.retire
    return .ok chosen

/--
Removes a connection from the client and closes its request channel.
-/
private def retireConnection (client : Client) (connection : Connection) (origin : URI.Origin) :
    Async Unit := do
  client.state.atomically <| modify fun
    | some slot =>
      if slot.origin == origin && slot.connection.id == connection.id then none else some slot
    | none => none
  connection.close

namespace Impl

/--
The connection a request is currently dispatched on, together with the origin it was opened for.
A redirect chain carries one of these and replaces it whenever a hop needs a connection of its own.
-/
private structure Hop where
  connection : Connection
  origin : URI.Origin

private def buildRedirectRequest (plan : RedirectPlan)
    (request : Request Body.Any) : Async (Request Body.Any) := do
  let newBody : Body.Any ← match plan.bodyAction with
    | .empty => pure (Body.Any.ofBody Body.Empty.mk)
    | .replay => do
      request.body.reset?.getD (pure ())
      pure request.body
  return {
    line := { request.line with uri := plan.target, method := plan.method, headers := plan.headers }
    body := newBody
    extensions := request.extensions
  }

private def toAbsoluteForm {t : Type} (request : Request t)
    (scheme : URI.Scheme) (host : URI.Host) (port : UInt16) : Request t :=
  match request.line.uri with
  | .originForm path query =>
    { request with
        line := { request.line with uri := .absoluteForm {
          scheme,
          path,
          query := query,
          authority := some { host, port := .value port }
          fragment := none
        }
      }
    }
  | _ => request

-- Normalize absolute-form URIs back to origin-form for direct (non-proxy) connections.
-- RFC 9112 §3.2.2: servers for direct connections expect origin-form; absolute-form is
-- only required when sending through an HTTP proxy.
private def toOriginForm {t : Type} (request : Request t) : Request t :=
  match request.line.uri with
  | .absoluteForm af =>
    { request with line := { request.line with uri := .originForm af.path af.query } }
  | _ => request

private def rewriteForProxy (hop : Hop) (request : Request Body.Any) : Request Body.Any :=
  if hop.connection.config.proxy.isSome then
    toAbsoluteForm request hop.origin.scheme hop.origin.host hop.origin.port
  else
    toOriginForm request

-- RFC 9112 §3.2 requires a `Host` on every HTTP/1.1 request, and only this layer knows the origin
-- the hop is dispatched to. Redirect planning deliberately rewrites `Host` only when the request
-- already had one, so a chain that started without it would otherwise reach a new host bare.
private def withHostHeader (hop : Hop) (request : Request Body.Any) : Request Body.Any :=
  if request.line.headers.contains .host then
    request
  else
    { request with
        line := { request.line with
          headers := request.line.headers.insert .host (.ofString! hop.origin.hostHeader) } }

/--
`true` when the connection that delivered `head` survives the exchange, so the next hop of a
redirect chain may reuse it. A response either asks for closure outright or ends its body at the
close: RFC 9112 §6.3 gives a response carrying neither `Content-Length` nor `Transfer-Encoding` no
other framing, unless its status forbids content in the first place.

`config` decides this as much as the response does: a client with `enableKeepAlive := false` asked
for closure itself, and the connection is retired no matter how obliging the server's head is.
-/
private def allowsConnectionReuse (config : Config) (head : Response.Head) : Bool :=
  let bodyless :=
    head.status.isInformational ∨ head.status == .noContent ∨ head.status == .notModified
  config.enableKeepAlive ∧ Message.Head.shouldKeepAlive (dir := .sending) head ∧
    (bodyless ∨ (Message.Head.getSize (dir := .sending) head (allowEOFBody := false)).isSome)

/--
Performs one request/response hop through the middleware chain. Failures flow through the
chain as a typed `Except Error`; an exception thrown by a middleware itself is wrapped
as `Error.io`.

Connection cleanup is owned entirely by this function: on a failed hop the connection is retired
exactly once, and on a successful hop a background task watches the exchange completion and retires
the connection if the transport errors after the response was delivered. The completion promise of
the innermost send is captured in a ref because middlewares only see the response: a hop that
short-circuits without sending has no completion to watch. It is also returned, so a redirect chain
can wait for the exchange to finish before reusing the connection.
-/
private def dispatchHop (client : Client) (hop : Hop) (request : Request Body.Any)
    (overrides : RequestOverrides) :
    Async (Except Error (Response Body.Stream × Option (IO.Promise (Except Error Unit)))) := do
  let completionRef ← IO.mkRef (none : Option (IO.Promise (Except Error Unit)))
  let inner : Request Body.Any → Async (Except Error (Response Body.Stream)) :=
      fun req => do
    match ← hop.connection.sendTracked req overrides with
    | .ok (response, completion) =>
      completionRef.set (some completion)
      return .ok response
    | .error e => return .error e
  let chain := client.middlewares.foldr (fun mw next req => mw req next) inner
  match ← try chain request catch err => pure (.error (.io err)) with
  | .ok response =>
    let completion ← completionRef.get
    if let some completion := completion then
      background do
        if let .error _ ← await completion.result! then
          client.retireConnection hop.connection hop.origin
    return .ok (response, completion)
  | .error e =>
    client.retireConnection hop.connection hop.origin
    return .error e

/--
Canonical string key for a request target used by cycle detection. The origin is tracked
separately in the history tuple, so this drops the authority and keys only on the path and query.
Both origin-form and absolute-form targets normalize to the same string so that a redirect chain
that alternates between direct (origin-form) and cross-origin (absolute-form) hops is still detected
as a cycle.
-/
private def targetKey : RequestTarget → String
  | .absoluteForm af => toString (RequestTarget.originForm af.path af.query)
  | t => toString t

/--
Decides whether `response` continues the redirect chain, given the effective `config` for this
request. Returns the plan to follow, or `none` when the response is delivered to the caller as-is:
the hop budget is spent, the response is not a followable redirect, or the target was already
visited.
-/
private def evaluateRedirect (hop : Hop) (config : Config) (request : Request Body.Any)
    (response : Response Body.Stream) (remaining : Nat)
    (history : Array (URI.Origin × String)) : Option RedirectPlan := Id.run do
  if remaining = 0 then return none

  let .follow plan :=
      decideRedirect hop.origin request.line request.body.reset?.isSome config.onlySafeRedirects
        response.line.version response.line.status response.line.headers
    | return none

  if history.contains (plan.origin, targetKey plan.target) then return none

  return some plan

/--
Points the chain at the connection the next hop must use: the current one when the hop stays on
this origin and the redirect response left it usable, otherwise a fresh one for the plan's origin,
with the outgoing connection retired first.
-/
private def advanceHop (client : Client) (hop : Hop) (config : Config) (plan : RedirectPlan)
    (response : Response Body.Stream) : Async (Except Error Hop) := do
  if !plan.isCrossOrigin ∧ allowsConnectionReuse config response.line then
    if !(← hop.connection.isClosed) then return .ok hop

  client.retireConnection hop.connection hop.origin
  match ← client.getOrCreateConnection plan.origin with
  | .error e => return .error e
  | .ok connection => return .ok { connection, origin := plan.origin }

private partial def sendWithRedirects
    (client : Client) (hop : Hop) (request : Request Body.Any)
    (remaining : Nat) (overrides : RequestOverrides)
    (history : Array (URI.Origin × String) := #[]) :
    Async (Except Error (Response Body.Stream)) := do

  -- Recomputed per hop: a cross-origin swap may land on a connection with a different `Config`.
  let config := overrides.apply hop.connection.config
  let history := history.push (hop.origin, targetKey request.line.uri)
  let request := withHostHeader hop (rewriteForProxy hop request)

  match ← dispatchHop client hop request overrides with
  | .error e => return .error e
  | .ok (response, completion) =>
    match evaluateRedirect hop config request response remaining history with
    | none => return .ok response
    | some plan =>
      -- Draining the redirect body and rebuilding the request run user-supplied `Body` code;
      -- an exception thrown there must still retire the checked-out connection.
      let drainLimit := config.redirectBodyDrainLimit.toUInt64
      let next : Except Error (Hop × Request Body.Any) ←
        try
          response.body.drain (drainLimit := some drainLimit)
            (closeStream := response.body.close)
          if let some completion := completion then
            discard <| await completion.result!
          let newRequest ← buildRedirectRequest plan request
          match ← advanceHop client hop config plan response with
          | .error e => pure (.error e)
          | .ok hop => pure (.ok (hop, newRequest))
        catch err =>
          client.retireConnection hop.connection hop.origin
          pure (.error (.io err))
      match next with
      | .error e => return .error e
      | .ok (hop, newRequest) =>
        sendWithRedirects client hop newRequest (remaining - 1) overrides history

end Impl

/--
Sends a request to `origin`, following redirects and applying middlewares, returning the response
or the typed `Error` that ended the exchange.

On a retryable connection-level failure (see `Error.isRetryable`), retries up to `client.maxRetries`
times on fresh connections. Application-level failures (timeouts, protocol violations, body-size
limits) are never retried.

A failed hop, a cross-origin redirect swap, or a connection error after the final response retires
the connection, so the client holds at most one live origin at a time.
-/
def trySend {β : Type} [Coe β Body.Any] (client : Client) (origin : URI.Origin)
    (request : Request β) (overrides : RequestOverrides := {}) :
    Async (Except Error (Response Body.Stream)) := do
  let request : Request Body.Any := { request with }

  let reset? := request.body.reset?
  let retries := if request.line.method.isIdempotent && reset?.isSome then client.maxRetries else 0

  let attempts := retries + 1

  let attemptOnce : Async (Except Error (Response Body.Stream)) := do
    match ← client.getOrCreateConnection origin with
    | .error e => return .error e
    | .ok connection =>
      let config := overrides.apply connection.config
      Impl.sendWithRedirects client { connection, origin } request config.maxRedirects overrides

  for attempt in 0...attempts do
    if attempt > 0 then
      if let some reset := reset? then
        reset

    match ← attemptOnce with
    | .ok response => return .ok response
    | .error e =>
      if ¬e.isRetryable || attempt + 1 ≥ attempts then
        return .error e

  return .error (.io (IO.userError "HTTP client retry loop exhausted without returning"))

/--
Sends a request to `origin`, following redirects and applying middlewares.
Use `trySend` to receive failures as a typed `Error` instead of a thrown exception.
-/
def send {β : Type} [Coe β Body.Any] (client : Client) (origin : URI.Origin) (request : Request β)
    (overrides : RequestOverrides := {}) : Async (Response Body.Stream) :=
  client.trySend origin request overrides >>= Error.throwOrPure

end Client
end Std.Http
