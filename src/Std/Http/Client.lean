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
public import Init.Data.Queue
import Init.Data.Array

public section

/-!
# Client

An HTTP/1.1 client that opens connections, reuses them across requests, follows redirects, and
retries connection-level failures.

The client keeps a pool of connections for each origin it talks to. A request checks out an idle
connection to its origin, or opens a new one while the origin has fewer than
`Config.maxConnectionsPerOrigin`, or else waits for one to come free; each connection carries one
exchange at a time and goes back to the pool when that exchange ends. Idle connections close
themselves after `Config.keepAliveTimeout`. Transport establishment is delegated to a `Connector`,
so plain TCP, TLS, and mock transports all plug in the same way.

Use `Client.new` to create a client, then `client.send` to dispatch requests.
-/

set_option linter.all true

namespace Std.Http.Client

open Std Async TCP Protocol H1
open Time

/--
A middleware intercepts every request/response hop performed by a `Client`, redirect hops included.

The function receives the origin the hop is addressed to, the outgoing request, and a `next`
continuation that performs the actual send. Call `next req` to forward the (possibly modified)
request downstream; the result carries either the response or the typed `Error` that ended the hop,
which the middleware may inspect, replace, or recover from. Return `.ok response` without calling
`next` to short-circuit the chain.

A redirect can lead to another origin, and the client strips credentials from a cross-origin hop
before the middleware runs. A middleware that adds credentials must therefore check the origin, or
be wrapped in `Middleware.forOrigin`, or it hands them to whatever host a redirect names.

Middlewares are composed outermost-first: the first element in the array wraps all subsequent ones.
A middleware that calls `next` again is done with the previous response.
-/
abbrev Middleware :=
  URI.Origin → Request Body.Any → (Request Body.Any → Async (Except Error (Response Body.Stream))) →
    Async (Except Error (Response Body.Stream))

/--
Applies `middleware` only to hops addressed to `origin`, passing every other hop straight through.
-/
def Middleware.forOrigin (origin : URI.Origin) (middleware : Middleware) : Middleware :=
  fun hopOrigin request next =>
    if hopOrigin == origin then middleware hopOrigin request next else next request

/--
What a request waiting at `Config.maxConnectionsPerOrigin` is eventually handed.
-/
inductive Grant where
  /--
  A connection whose exchange just ended, handed over instead of going back to the idle set.
  -/
  | idle (connection : Connection)

  /--
  A connection closed, and its place under the limit passes to the waiting request, which opens a
  connection of its own.
  -/
  | vacancy

  /--
  `Client.close` ran while the request was waiting.
  -/
  | closed

instance : Inhabited Grant := ⟨.closed⟩

/--
The connections a client holds for one origin, and the requests waiting for one of them.
-/
structure OriginPool where
  /--
  The origin every connection here was opened for.
  -/
  origin : URI.Origin

  /--
  Every connection opened here and not yet removed: idle, carrying an exchange, or closed with its
  loop's exit not yet processed. Each holds a place under the limit until it is removed.
  -/
  connections : Array Connection := #[]

  /--
  The connections with no exchange in flight, most recently returned last.
  -/
  idle : Array Connection := #[]

  /--
  Connections being opened. They count against the limit before they exist.
  -/
  connecting : Nat := 0

  /--
  Requests waiting for a connection, oldest first.
  -/
  waiters : Std.Queue (IO.Promise Grant) := .empty

namespace OriginPool

/--
The number of connections `Config.maxConnectionsPerOrigin` bounds: open ones and ones being opened.
-/
def size (pool : OriginPool) : Nat :=
  pool.connections.size + pool.connecting

/--
`true` when the pool has no connection and no waiting request, so the client can drop it.
-/
def isUnused (pool : OriginPool) : Bool :=
  pool.size == 0 ∧ pool.waiters.isEmpty

end OriginPool

end Std.Http.Client

namespace Std.Http

open Std Async

/--
An HTTP client: a pool of reusable connections per origin, the configuration used to open new ones,
and the redirect/retry policy applied to every request.
-/
structure Client where
  /--
  The pool for each origin with a connection, a connection being opened, or a waiting request.
  -/
  pools : Mutex (Array Client.OriginPool)

  /--
  Configuration used when creating new connections.
  -/
  config : Client.Config

  /--
  Monotonically increasing counter for unique connection IDs.
  -/
  nextId : Mutex UInt64

  /--
  The number of times `close` has run. A request that started before a `close` is not retried after
  it, and a connection that finishes opening after one is closed instead of used.
  -/
  closes : IO.Ref Nat

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
    (maxRetries : Nat := 1) (middlewares : Array Middleware := #[]) :
    Async Client := do
  let pools ← Mutex.new (#[] : Array OriginPool)
  let nextId ← Mutex.new (1 : UInt64)
  let closes ← IO.mkRef 0
  pure { pools, config, nextId, closes, middlewares, connect, maxRetries }

/--
Closes every connection the client holds, aborting the exchanges in flight on them, and fails every
request already started: those waiting for a connection, those whose connection is still being
opened, and those in flight, none of which is retried. The client remains usable: a later `send`
opens fresh connections.
-/
def close (client : Client) : Async Unit := do
  client.closes.modify (· + 1)
  let (connections, waiters) ← client.pools.atomically do
    let pools ← get
    set (pools.filterMap fun pool =>
      let pool := { pool with idle := #[], waiters := .empty }
      if pool.isUnused then none else some pool)
    return (pools.flatMap (·.connections), pools.flatMap (·.waiters.toArray))
  for grant in waiters do
    grant.resolve .closed
  for connection in connections do
    connection.close

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
      client.connect origin client.config
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
Runs `f` on the pool for `origin` under the client's lock, starting from an empty pool when there is
none, and drops the pool once `f` leaves it unused.

`f` runs with the lock held, so it must not resolve a promise or act on a connection beyond asking
`isClosed`: a continuation that ran inline could take the lock again.
-/
private def modifyPool (client : Client) (origin : URI.Origin)
    (f : OriginPool → BaseIO (α × OriginPool)) : BaseIO α :=
  client.pools.atomically do
    let pools ← get
    let index? := pools.findIdx? (·.origin == origin)
    let pool := (index?.bind (pools[·]?)).getD { origin }
    let (result, pool) ← f pool
    set <| match index?, pool.isUnused with
      | some index, true => pools.eraseIdx! index
      | some index, false => pools.set! index pool
      | none, true => pools
      | none, false => pools.push pool
    return result

/--
Takes the most recently returned connection off `idle`, skipping any that has closed since. Older
idle connections are left to reach their keep-alive timeout.
-/
private partial def takeIdle (idle : Array Connection) :
    BaseIO (Option Connection × Array Connection) := do
  let some connection := idle.back? | return (none, idle)
  if ← connection.isClosed then
    takeIdle idle.pop
  else
    return (some connection, idle.pop)

/--
How a request gets its connection, as decided under the client's lock.
-/
private inductive Checkout where
  | reuse (connection : Connection)
  | dial
  /--
  Close `idle`, an idle connection taken out of the idle set to make room, and wait for a place: its
  own, once its loop exits, unless an older waiting request takes it first.
  -/
  | replace (idle : Connection) (grant : IO.Promise Grant)
  | wait (grant : IO.Promise Grant)

/--
Passes a place under the per-origin limit that `pool` has just freed to its oldest waiting request,
which then opens a connection in it.
-/
private def passPlace (pool : OriginPool) : Option (IO.Promise Grant) × OriginPool :=
  match pool.waiters.dequeue? with
  | some (grant, waiters) => (some grant, { pool with waiters, connecting := pool.connecting + 1 })
  | none => (none, pool)

/--
Gives back the place a connection was being opened in, after the open failed or was abandoned.
-/
private def abandonDial (client : Client) (origin : URI.Origin) : BaseIO Unit := do
  let waiter ← client.modifyPool origin fun pool =>
    return passPlace { pool with connecting := pool.connecting - 1 }
  if let some grant := waiter then
    grant.resolve .vacancy

/--
Removes a connection whose loop has exited, freeing its place under the limit. A connection already
taken out of the pool to make room for another has given up its place, and is ignored.
-/
private def forget (client : Client) (origin : URI.Origin) (connection : Connection) : BaseIO Unit := do
  let waiter ← client.modifyPool origin fun pool => do
    unless pool.connections.any (·.id == connection.id) do return (none, pool)
    return passPlace { pool with
      connections := pool.connections.filter (·.id != connection.id)
      idle := pool.idle.filter (·.id != connection.id) }
  if let some grant := waiter then
    grant.resolve .vacancy

/--
Returns a connection whose exchange has ended to the pool: to the oldest waiting request, or else to
the idle set. A connection that can carry no further request is left alone; its loop's exit removes
it from the pool.
-/
private def checkin (client : Client) (origin : URI.Origin) (connection : Connection) : BaseIO Unit := do
  let waiter ← client.modifyPool origin fun pool => do
    if ← connection.isClosed then return (none, pool)
    unless pool.connections.any (·.id == connection.id) do return (none, pool)
    match pool.waiters.dequeue? with
    | some (grant, waiters) => return (some grant, { pool with waiters })
    | none => return (none, { pool with idle := pool.idle.push connection })
  if let some grant := waiter then
    grant.resolve (.idle connection)

/--
Opens a connection in the place a checkout reserved for it and adds it to the pool. On failure the
place is given back, and so is a connection that finishes opening after `close` has run.
-/
private def dial (client : Client) (origin : URI.Origin) : Async (Except Error Connection) := do
  let closes ← client.closes.get
  let opened ← try client.openConnection origin catch err => pure (.error (.io err))
  match opened with
  | .error e =>
    client.abandonDial origin
    return .error e
  | .ok connection =>
    client.modifyPool (α := Unit) origin fun pool =>
      return ((), { pool with
        connecting := pool.connecting - 1
        connections := pool.connections.push connection })
    -- However the connection ends, its loop exits, and that is when the pool lets it go.
    BaseIO.chainTask connection.shutdown.result? fun _ => client.forget origin connection
    if (← client.closes.get) != closes then
      connection.close
      return .error (.closed "client closed while the connection was being opened")
    return .ok connection

/--
Checks out a connection to `origin` for one exchange: an idle one when the pool has one, a new one
while the origin is under `Config.maxConnectionsPerOrigin`, and otherwise the next one another
request gives back. The caller owns the connection until it passes it to `release` or
`releaseWhenDone`.

A `fresh` checkout, used to retry a failed request, never reuses an idle connection, which may have
gone stale the same way. At the limit it closes the least recently used idle connection to make room,
and waits for a place like any other request; a closing connection keeps its place until its loop
exits, so the limit also bounds connections being torn down.
-/
private def acquire (client : Client) (origin : URI.Origin) (fresh : Bool := false) :
    Async (Except Error Connection) := do
  let limit := client.config.maxConnectionsPerOrigin.val
  let checkout ← client.modifyPool (α := Checkout) origin fun pool => do
    if !fresh then
      let (connection, idle) ← takeIdle pool.idle
      if let some connection := connection then
        return (.reuse connection, { pool with idle })
    if pool.size < limit then
      return (.dial, { pool with connecting := pool.connecting + 1 })
    let grant ← IO.Promise.new
    let pool := { pool with waiters := pool.waiters.enqueue grant }
    if fresh then
      if let some oldest := pool.idle[0]? then
        return (.replace oldest grant, { pool with idle := pool.idle.extract 1 })
    return (.wait grant, pool)
  let grant ← match checkout with
    | .reuse connection => return .ok connection
    | .dial => return (← client.dial origin)
    | .replace idle grant =>
      idle.close
      pure grant
    | .wait grant => pure grant
  match ← await grant.result! with
  | .idle connection => return .ok connection
  | .vacancy => client.dial origin
  | .closed => return .error (.closed "client closed while the request waited for a connection")

/--
Ends a request's hold on `connection`: back to the pool when `reusable`, and closed otherwise.
-/
private def release (client : Client) (origin : URI.Origin) (connection : Connection)
    (reusable : Bool) : Async Unit :=
  if reusable then client.checkin origin connection else connection.close

/--
Returns `connection` to the pool once `completion` reports its exchange finished. The check-in runs
synchronously as the connection resolves `completion`, which for an exchange that ends normally
happens before the caller's response body ends (see `InFlightState.finishedStream`), so a caller that
reads its body to the end and sends again finds the connection idle. An exchange that failed leaves
the connection to its loop, which is exiting.
-/
private def releaseWhenDone (client : Client) (origin : URI.Origin) (connection : Connection)
    (completion : IO.Promise (Except Error Unit)) : BaseIO Unit :=
  BaseIO.chainTask (sync := true) completion.result? fun
    | some (.ok ()) => client.checkin origin connection
    | _ => pure ()

namespace Impl

/--
An exchange a hop ran: the connection it checked out, and the promise that resolves once that
connection has finished with the exchange.
-/
private structure Exchange where
  connection : Connection
  completion : IO.Promise (Except Error Unit)

private def buildRedirectRequest (plan : RedirectPlan)
    (request : Request Body.Any) : Async (Request Body.Any) := do
  let newBody : Body.Any ← match plan.bodyAction with
    -- Replayable, so that an authenticator can still answer a challenge on the next hop.
    | .empty => pure (Body.Any.ofReplayableBody Body.Empty.mk)
    | .replay => do
      request.body.reset?.getD (pure ())
      pure request.body
  -- `Expect: 100-continue` asks to wait before sending content, and RFC 9110 §10.1.1 forbids it on a
  -- request that has none.
  let headers := match plan.bodyAction with
    | .empty => plan.headers.erase .expect
    | .replay => plan.headers
  return {
    line := { request.line with uri := plan.target, method := plan.method, headers }
    body := newBody
    extensions := request.extensions
  }

/--
Performs one request/response hop to `origin` through the middleware chain. Failures flow through
the chain as a typed `Except Error`; an exception thrown by a middleware itself is wrapped
as `Error.io`.

A connection is checked out only when the chain calls through to the network, so a middleware that
answers by itself leaves the pool alone; `fresh` is passed on to that checkout. A failed exchange
closes its connection, including one ended by an exception from user code it runs (a cookie handler,
an authenticator, a body's reset). A middleware that calls through again is done with the earlier
exchange, whose connection goes back to the pool once that exchange ends. The hop returns the last
exchange, recorded in a ref because middlewares only see the response, and the caller gives its
connection back once it ends.
-/
private def dispatchHop (client : Client) (initialOrigin origin : URI.Origin)
    (request : Request Body.Any) (overrides : RequestOverrides) (answered : IO.Ref Bool)
    (fresh : Bool := false) :
    Async (Except Error (Response Body.Stream × Option Exchange)) := do
  let exchangeRef ← IO.mkRef (none : Option Exchange)
  let inner : Request Body.Any → Async (Except Error (Response Body.Stream)) :=
      fun req => do
    if let some previous ← exchangeRef.get then
      exchangeRef.set none
      client.releaseWhenDone origin previous.connection previous.completion
    match ← client.acquire origin fresh with
    | .error e => return .error e
    | .ok connection =>
      let sent ←
        try connection.sendTracked req overrides (some initialOrigin)
        catch err => do
          connection.close
          throw err
      match sent with
      | .ok tracked =>
        answered.set true
        exchangeRef.set (some { connection, completion := tracked.completion })
        return .ok tracked.response
      | .error e =>
        connection.close
        return .error e
  let chain := client.middlewares.foldr (fun mw next req => mw origin req next) inner
  let outcome ← try chain request catch err => pure (.error (.io err))
  let exchange ← exchangeRef.get
  match outcome with
  | .ok response => return .ok (response, exchange)
  | .error e =>
    -- A middleware failed the hop after an exchange delivered a response nobody will read.
    exchange.forM (·.connection.close)
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
Decides whether `response` continues the redirect chain. Returns the plan to follow, or `none` when
the response is delivered to the caller as-is: the hop budget is spent, the response is not a
followable redirect, or the chain already sent the same method to the same target. The method is
part of what was visited, so a `POST` answered with `303` to its own URL is followed with `GET`.
-/
private def evaluateRedirect (origin : URI.Origin) (request : Request Body.Any)
    (response : Response Body.Stream) (remaining : Nat)
    (history : Array (URI.Origin × Method × String)) : Option RedirectPlan := Id.run do
  if remaining = 0 then return none

  -- Several `Location` fields name no single target; picking one would be a guess.
  if ((response.line.headers.getAll? .location).map (·.size)).getD 0 > 1 then return none

  let .follow plan :=
      decideRedirect origin request.line request.body.reset?.isSome
        response.line.version response.line.status response.line.headers
    | return none

  if history.contains (plan.origin, plan.method, targetKey plan.target) then return none

  return some plan

private partial def sendWithRedirects
    (client : Client) (initialOrigin origin : URI.Origin) (request : Request Body.Any)
    (remaining : Nat) (overrides : RequestOverrides) (answered : IO.Ref Bool)
    (history : Array (URI.Origin × Method × String) := #[]) (fresh : Bool := false) :
    Async (Except Error (Response Body.Stream)) := do
  let history := history.push (origin, request.line.method, targetKey request.line.uri)

  match ← dispatchHop client initialOrigin origin request overrides answered fresh with
  | .error e => return .error e
  | .ok (response, exchange) =>
    match evaluateRedirect origin request response remaining history with
    | none =>
      exchange.forM fun exchange =>
        client.releaseWhenDone origin exchange.connection exchange.completion
      return .ok response
    | some plan =>
      -- Draining runs user-supplied `Body` code, and an exception thrown there must still end the
      -- hold on the connection. A body abandoned at the drain limit is left on its connection,
      -- which is closed rather than waited on while it reads the rest.
      let config := overrides.apply ((exchange.map (·.connection.config)).getD client.config)
      let drainLimit := config.intermediateBodyDrainLimit.toUInt64
      let drained : Except IO.Error Bool ←
        try
          let overLimit ← IO.mkRef false
          response.body.drain (drainLimit := some drainLimit)
            (closeStream := do overLimit.set true; response.body.close)
          if ← overLimit.get then
            pure (.ok false)
          else
            match exchange with
            | none => pure (.ok true)
            | some exchange =>
              match ← await exchange.completion.result! with
              | .ok () => pure (.ok true)
              | .error _ => pure (.ok false)
        catch err =>
          pure (.error err)
      match drained with
      | .error err =>
        exchange.forM (·.connection.close)
        -- A body cut short fails because its exchange did, and the exchange's error says how, in the
        -- typed form a retry is decided on.
        if let some exchange := exchange then
          if let .error e ← await exchange.completion.result! then
            return .error e
        return .error (.io err)
      | .ok reusable =>
        exchange.forM fun exchange => client.release origin exchange.connection reusable
        let newRequest : Except IO.Error (Request Body.Any) ←
          try pure (.ok (← buildRedirectRequest plan request)) catch err => pure (.error err)
        match newRequest with
        | .error err => return .error (.io err)
        | .ok newRequest =>
          sendWithRedirects client initialOrigin plan.origin newRequest (remaining - 1) overrides
            answered history

end Impl

/--
Sends a request to `origin`, following redirects and applying middlewares, returning the response
or the typed `Error` that ended the exchange.

On a retryable connection-level failure (see `Error.isRetryable`), retries up to `client.maxRetries`
times on fresh connections, unless `close` ran since the request started. A request with an
idempotent method and a replayable body is retried after any such failure; any other request only
when the failure proves it never reached a peer (`Error.isNeverSent`) and no response has arrived
for it. Application-level failures (timeouts, protocol violations, body-size limits) are never
retried.

Every attempt, and every redirect hop, checks out a connection to its origin from the client's pool.
A connection goes back to the pool when its exchange completes, and leaves it when the exchange
fails.
-/
def trySend {β : Type} [Coe β Body.Any] (client : Client) (origin : URI.Origin)
    (request : Request β) (overrides : RequestOverrides := {}) :
    Async (Except Error (Response Body.Stream)) := do
  let request : Request Body.Any := { request with }
  let closes ← client.closes.get

  -- An absolute-form target names its own origin. Sending it to another would let the target and the
  -- connection disagree: through a proxy it would reach the target's host carrying the cookies and
  -- credentials of `origin`.
  if let .absoluteForm uri := request.line.uri then
    unless uri.origin? == some origin do
      return .error (.invalidRequest
        s!"request target {request.line.uri} does not belong to the origin it is sent to, {origin}")

  let reset? := request.body.reset?
  let replayable := request.line.method.isIdempotent && reset?.isSome
  let attempts := client.maxRetries + 1

  let maxRedirects := (overrides.apply client.config).maxRedirects

  for attempt in 0...attempts do
    if attempt > 0 then
      if let some reset := reset? then
        -- Rewinding runs the body's own code; its failure is the request's, reported typed.
        try reset catch err => return .error (.io err)

    -- Set once any hop of this attempt got a response: from then on the request, or the one it was
    -- redirected from, has reached a peer.
    let answered ← IO.mkRef false
    match ← Impl.sendWithRedirects client origin origin request maxRedirects overrides answered
        (fresh := attempt > 0) with
    | .ok response => return .ok response
    | .error e =>
      let mayResend := replayable ∨ (e.isNeverSent ∧ ¬(← answered.get))
      if ¬e.isRetryable ∨ ¬mayResend ∨ attempt + 1 ≥ attempts ∨ (← client.closes.get) != closes then
        return .error e

  return .error (.io (IO.userError "HTTP client retry loop exhausted without returning"))

/--
Sends a request to `origin`, following redirects and applying middlewares.
Use `trySend` to receive failures as a typed `Error` instead of a thrown exception.
-/
def send {β : Type} [Coe β Body.Any] (client : Client) (origin : URI.Origin) (request : Request β)
    (overrides : RequestOverrides := {}) : Async (Response Body.Stream) :=
  client.trySend origin request overrides >>= Error.throwOrPure

/--
Sends a request whose target is an absolute URL (`http://host:8080/path?query`) to the origin that URL
names, like `trySend` with that origin. The target goes on the wire in origin-form (or in the
absolute-form a proxy needs), so any user information and fragment in the URL are not sent. Fails with
`Error.invalidRequest` when the target is not an absolute URL with a host.
-/
def tryExecute {β : Type} [Coe β Body.Any] (client : Client) (request : Request β)
    (overrides : RequestOverrides := {}) : Async (Except Error (Response Body.Stream)) := do
  let request : Request Body.Any := { request with }
  let .absoluteForm uri := request.line.uri
    | return .error (.invalidRequest
        s!"request target {request.line.uri} is not an absolute URL; use `trySend` with an origin")
  let some origin := uri.origin?
    | return .error (.invalidRequest s!"request target {request.line.uri} names no host")
  let request := { request with line := { request.line with uri := uri.originTarget } }
  client.trySend origin request overrides

/--
Sends a request whose target is an absolute URL to the origin that URL names.
Use `tryExecute` to receive failures as a typed `Error` instead of a thrown exception.
-/
def execute {β : Type} [Coe β Body.Any] (client : Client) (request : Request β)
    (overrides : RequestOverrides := {}) : Async (Response Body.Stream) :=
  client.tryExecute request overrides >>= Error.throwOrPure

/--
Sends a `GET` for `url` (`http://host:8080/path?query`). Fails with `Error.invalidRequest` when `url`
is not an absolute URL with a host.
-/
def tryGet (client : Client) (url : String) (overrides : RequestOverrides := {}) :
    Async (Except Error (Response Body.Stream)) := do
  let some uri := URI.parse? url
    | return .error (.invalidRequest s!"not an absolute URL: {url.quote}")
  client.tryExecute (← Request.get (.absoluteForm uri) |>.empty) overrides

/--
Sends a `GET` for `url` (`http://host:8080/path?query`).
Use `tryGet` to receive failures as a typed `Error` instead of a thrown exception.
-/
def get (client : Client) (url : String) (overrides : RequestOverrides := {}) :
    Async (Response Body.Stream) :=
  client.tryGet url overrides >>= Error.throwOrPure

end Client
end Std.Http
