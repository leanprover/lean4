/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Http.Client.Agent
public import Std.Http.Client.Connector
import Init.Data.Array

public section

/-!
# Pool

A simple connection pool that keeps at most one reusable session.

If the next request targets the current session's origin, the session is reused. If the origin
changes, the current session is retired and a new session is opened for the new origin.

Use `Pool.new` to create a pool, then call `pool.send` to dispatch requests through managed
sessions. The pool handles redirect following and middlewares.
-/

namespace Std.Http.Client

open Std Async TCP Protocol
open Time

set_option linter.all true

/--
The single reusable session currently held by the pool.
-/
structure Pool.Slot where

  /--
  Origin this session is connected to.
  -/
  origin : URI.Origin

  /--
  The current session.
  -/
  session : Session

/--
Default number of connection-level retries for pools and clients. One retry absorbs the
stale keep-alive race (the server closed a pooled connection just as it was reused)
without sending any request more than twice.
-/
def Pool.defaultMaxRetries : Nat := 1

/--
A connection pool that manages one reusable session at a time.
-/
structure Pool where

  /--
  Current reusable session, if any.
  -/
  state : Mutex (Option Pool.Slot)

  /--
  Configuration used when creating new sessions.
  -/
  config : Config

  /--
  Monotonically increasing counter for unique session IDs.
  -/
  nextId : Mutex UInt64

  /--
  Middlewares applied (outermost-first) around every request/response hop.
  -/
  middlewares : Array Middleware := #[]

  /--
  Function used to open new transport sessions. Supply a custom `Connector` via `Pool.new`.
  -/
  connect : Connector := Connector.tcp

  /--
  Maximum number of times to retry a failed request on a fresh connection. `0` disables
  retries.

  Retries only apply to connection-level failures (the session died before a response was
  received). Application-level errors (4xx, 5xx) are never retried automatically.

  **Only idempotent methods with replayable bodies are retried.** Requests whose method
  returns `false` from `Method.isIdempotent` (e.g. `POST`, `PATCH`) are never retried
  regardless of this value, to prevent unintended duplicate side-effects.
  -/
  maxRetries : Nat := Pool.defaultMaxRetries

namespace Pool

/--
Creates a new, empty connection pool. Supply a custom `connect` function (e.g. a TLS
connector or a mock) to customize how transport sessions are opened.
-/
def new (config : Config := {}) (connect : Connector := Connector.tcp)
    (maxRetries : Nat := Pool.defaultMaxRetries) (middlewares : Array Middleware := #[]) :
    Async Pool := do
  let state ← Mutex.new (none : Option Pool.Slot)
  let nextId ← Mutex.new (1 : UInt64)
  pure { state, config, nextId, middlewares, connect, maxRetries }

/--
Closes and removes the pool's current session, if any. The pool remains usable: a later
`send` simply opens a fresh connection.
-/
def close (pool : Pool) : Async Unit := do
  let slot ← pool.state.atomically <| modifyGet fun slot => (slot, none)
  if let some slot := slot then
    discard <| slot.session.close

/--
Acquires a fresh unique session ID.
-/
private def nextSessionId (pool : Pool) : Async UInt64 :=
  pool.nextId.atomically <| modifyGet fun id => (id, id + 1)

/--
Opens a new session for `origin` and assigns it a pool-local ID. The connector runs under
`Config.connectTimeout`, bounding DNS resolution and the transport connect. An exception
thrown by a custom connector is reported as `Error.connect`, keeping every connector-level
failure typed on one path.
-/
private def openSession (pool : Pool) (origin : URI.Origin) : Async (Except Error Session) := do
  let resultChannel : Std.Channel (Except Error Session) ← Std.Channel.new

  let connectTask ← async (t := AsyncTask) do
    try
      pool.connect origin.scheme origin.host origin.port pool.config
    catch err =>
      pure (.error (.connect (toString err)))

  BaseIO.chainTask connectTask fun
    | .ok result => discard <| resultChannel.send result
    | .error err => discard <| resultChannel.send (.error (.connect (toString err)))

  let outcome ← Selectable.one #[
    .case resultChannel.recvSelector (fun result => pure (some result)),
    .case (← Selector.sleep pool.config.connectTimeout.val) (fun _ => pure none)
  ]

  match outcome with
  | some (.ok session) =>
    let id ← nextSessionId pool
    return .ok { session with id }
  | some (.error e) => return .error e
  | none =>
    -- The connector may still complete after the timeout; drain its result in the
    -- background and close the late session so the transport does not leak.
    background do
      let late ← Selectable.one #[.case resultChannel.recvSelector pure]
      if let .ok session := late then
        discard <| session.close
    return .error (.connect
      s!"connecting to {origin.host}:{origin.port} timed out after {pool.config.connectTimeout.val}ms")

/--
Returns the pool's single session for `origin`.

If the current session has the same origin, it is checked out again; HTTP/1.1 requests
queue on the session. If the origin differs, the current session is retired and replaced.

A new session is opened *outside* the state mutex: DNS resolution and the TCP connect can block,
and holding the lock across them would serialize every other pool operation (including session
retirement). The lock is taken only for the brief fast-path check and to install the freshly
opened session.
-/
def getOrCreateSession (pool : Pool) (origin : URI.Origin) : Async (Except Error Session) := do
  -- Fast path: reuse an existing same-origin session without opening anything. A parked session
  -- whose background loop has already shut down (server EOF, idle keep-alive timeout) is evicted
  -- instead of returned: handing it out would fail the request even though nothing was ever
  -- written to the wire for it. A session can still die between this check and the actual send;
  -- that residual race surfaces as a connection error handled by the retry policy in `send`.
  let existing ← pool.state.atomically do
    match ← get with
    | some slot =>
      if slot.origin == origin then
        if ← slot.session.isClosed then
          set (none : Option Pool.Slot)
          pure none
        else
          pure (some slot.session)
      else
        pure none
    | none => pure none
  if let some session := existing then
    return .ok session

  -- Slow path: open a new session with the lock released.
  match ← pool.openSession origin with
  | .error e => return .error e
  | .ok session =>

    -- Install it, retiring whatever is parked. If another task installed a same-origin session
    -- while we were connecting, keep theirs and discard ours so the pool never holds two live
    -- sessions.
    let (chosen, evicted) ← pool.state.atomically do
      match ← get with
      | some slot =>
        if slot.origin == origin then
          pure (slot.session, some session)
        else
          set (some ({ origin, session } : Pool.Slot))
          pure (session, some slot.session)
      | none =>
        set (some ({ origin, session } : Pool.Slot))
        pure (session, none)
    if let some evictedSession := evicted then
      discard <| evictedSession.close
    return .ok chosen

/--
Removes a session from the pool and closes its request channel.
-/
private def retireSession (pool : Pool) (origin : URI.Origin) (session : Session) : Async Unit := do
  pool.state.atomically <| modify fun
    | some slot =>
      if slot.origin == origin && slot.session.id == session.id then none else some slot
    | none => none
  discard <| session.close

/--
Sends a request through the pooled session, following redirects and applying middlewares,
returning the response or the typed `Error` that ended the exchange.
On a retryable connection-level failure (see `Error.isRetryable`), retries up to
`pool.maxRetries` times on fresh connections. Application-level failures (timeouts,
protocol violations, body-size limits) are never retried.

Session lifecycle is owned by the agent driving the exchange: a failed hop, a cross-origin
redirect swap, or a connection error after the final response hands the session back to the
pool, which retires it. Cross-origin redirects keep the pool to one live origin at a time.
-/
def trySend {β : Type} [Coe β Body.Any] (pool : Pool) (origin : URI.Origin) (request : Request β)
    (overrides : RequestOverrides := {}) : Async (Except Error (Response Body.Stream)) := do
  -- Erase the body type once; every layer below the pool works with `Request Body.Any`.
  let request : Request Body.Any := { request with }

  -- Non-idempotent methods (POST, PATCH, …) must never be retried; a connection
  -- failure after partial delivery could cause duplicate side-effects.
  -- The body must also be replayable (`reset?`): the failed attempt may have consumed a
  -- streaming body, and retrying would silently send an empty or truncated body.
  let reset? := request.body.reset?
  let retries := if request.line.method.isIdempotent && reset?.isSome then pool.maxRetries else 0

  let attempts := retries + 1

  -- A single attempt: acquire a session and run the exchange. `Agent.trySend` owns session
  -- cleanup — every failure path inside it releases the session back to the pool — so the
  -- attempt only has to report the typed result to the retry loop below. Connection
  -- establishment is part of the attempt so that DNS/TCP failures are retried too.
  let attemptOnce : Async (Except Error (Response Body.Stream)) := do
    match ← pool.getOrCreateSession origin with
    | .error e => return .error e
    | .ok session =>
      Agent.trySend {
        session
        origin
        middlewares := pool.middlewares
        release := fun sess o => pool.retireSession o sess
        crossOrigin := .follow pool.getOrCreateSession
      } request overrides

  for attempt in 0...attempts do
    -- A prior attempt may have consumed (part of) the body; rewind it before resending.
    if attempt > 0 then
      if let some reset := reset? then
        reset
    match ← attemptOnce with
    | .ok response => return .ok response
    | .error e =>
      -- Report on the final attempt or for non-retryable failures;
      -- retryable failures fall through to the next attempt.
      if ¬e.isRetryable || attempt + 1 ≥ attempts then
        return .error e

  -- Unreachable: the loop runs at least once and the final attempt always returns.
  return .error (.io (IO.userError "HTTP client retry loop exhausted without returning"))

/--
Sends a request through the pooled session, following redirects and applying middlewares.
Use `trySend` to receive failures as a typed `Error` instead of a thrown exception.
-/
def send {β : Type} [Coe β Body.Any] (pool : Pool) (origin : URI.Origin) (request : Request β)
    (overrides : RequestOverrides := {}) : Async (Response Body.Stream) :=
  pool.trySend origin request overrides >>= Error.throwOrPure

end Pool
end Std.Http.Client
