/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Http.Client.Connection
public import Std.Http.Protocol.H1.Redirect
import Init.Data.Array

public section

/-!
# Agent

A transport-agnostic HTTP user-agent that wraps a `Connection` and adds automatic redirect
following.

`Agent` contains no TCP-specific code. Use `Agent.ofTransport` to create an `Agent` from
any connected transport.

Cross-origin redirect following is controlled by `CrossOriginPolicy`. A pool supplies
`.follow` callbacks; a standalone agent uses `.stop` (cross-origin redirects stop at the
first hop to a different origin).

When crossing to a different host the `Authorization` header is stripped from the redirected
request to prevent credential leakage.
-/

namespace Std.Http.Client

open Std Async TCP Protocol H1
open Time

set_option linter.all true

/--
A middleware intercepts every request/response hop performed by an `Agent`.

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
Policy for redirects that cross to a different origin (scheme, host, port).
-/
inductive CrossOriginPolicy where

  /--
  Stop at the first cross-origin hop: the redirect response is returned to the
  caller unfollowed.
  -/
  | stop

  /--
  Follow cross-origin redirects, calling `acquire` to open (or borrow from a
  pool) a connection to each new origin.
  -/
  | follow (acquire : URI.Origin → Async (Except Error Connection))

/--
An HTTP user-agent that manages a connection to a host and follows redirects.

The agent owns its connection's lifecycle: any hop that fails, any cross-origin
swap, and any transport error after a delivered response hands the connection to
`release` exactly once.
-/
structure Agent where
  /--
  The underlying HTTP connection.
  -/
  connection : Connection

  /--
  The origin (scheme, host, port) this agent is currently connected to.
  -/
  origin : URI.Origin

  /--
  Returns a connection the agent is done with: one that broke during a hop or was
  swapped out for a cross-origin redirect. A pool reclaims connections here; the
  default closes the connection.
  -/
  release : Connection → URI.Origin → Async Unit := fun connection _ => connection.close

  /--
  Policy for cross-origin redirects. With `.stop` (the default) they end the
  redirect chain and the 3xx response is returned as-is; a pool supplies
  `.follow` with its connection acquisition so the chain continues on a fresh
  connection.
  -/
  crossOrigin : CrossOriginPolicy := .stop

  /--
  Middlewares applied (outermost-first) around every request/response hop.
  An empty array means no interception.
  -/
  middlewares : Array Middleware := #[]

-- Implementation helpers live here in `namespace Client` so that `Agent` unambiguously
-- refers to the struct above, not to the `namespace Agent` opened below.
namespace Agent.Impl

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

private def rewriteForProxy (agent : Agent) (request : Request Body.Any) : Request Body.Any :=
  if agent.connection.config.proxy.isSome then
    toAbsoluteForm request agent.origin.scheme agent.origin.host agent.origin.port
  else
    toOriginForm request

-- RFC 9112 §3.2 requires a `Host` on every HTTP/1.1 request, and only this layer knows the origin
-- the hop is dispatched to. Redirect planning deliberately rewrites `Host` only when the request
-- already had one, so a chain that started without it would otherwise reach a new host bare.
private def withHostHeader (agent : Agent) (request : Request Body.Any) : Request Body.Any :=
  if request.line.headers.contains .host then
    request
  else
    { request with
        line := { request.line with
          headers := request.line.headers.insert .host (.ofString! agent.origin.hostHeader) } }

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

Connection cleanup is owned entirely by this function: on a failed hop the connection is handed to
`agent.release` exactly once, and on a successful hop a background task watches the exchange
completion and releases the connection if the transport errors after the response was delivered.
The completion promise of the innermost send is captured in a ref because middlewares only see
the response: a hop that short-circuits without sending has no completion to watch. It is also
returned, so a redirect chain can wait for the exchange to finish before reusing the connection.
-/
private def dispatchHop (agent : Agent) (request : Request Body.Any)
    (overrides : RequestOverrides) :
    Async (Except Error (Response Body.Stream × Option (IO.Promise (Except Error Unit)))) := do
  let completionRef ← IO.mkRef (none : Option (IO.Promise (Except Error Unit)))
  let inner : Request Body.Any → Async (Except Error (Response Body.Stream)) :=
      fun req => do
    match ← agent.connection.sendTracked req overrides with
    | .ok (response, completion) =>
      completionRef.set (some completion)
      return .ok response
    | .error e => return .error e
  let chain := agent.middlewares.foldr (fun mw next req => mw req next) inner
  match ← try chain request catch err => pure (.error (.io err)) with
  | .ok response =>
    let completion ← completionRef.get
    if let some completion := completion then
      background do
        if let .error _ ← await completion.result! then
          agent.release agent.connection agent.origin
    return .ok (response, completion)
  | .error e =>
    agent.release agent.connection agent.origin
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
the hop budget is spent, the response is not a followable redirect, the target was already visited,
or the hop needs a connection of its own that `agent.crossOrigin` cannot supply.
-/
private def evaluateRedirect (agent : Agent) (config : Config) (request : Request Body.Any)
    (response : Response Body.Stream) (remaining : Nat)
    (history : Array (URI.Origin × String)) : Option RedirectPlan := Id.run do
  if remaining = 0 then return none

  let .follow plan :=
      decideRedirect agent.origin request.line request.body.reset?.isSome config.onlySafeRedirects
        response.line.version response.line.status response.line.headers
    | return none

  if history.contains (plan.origin, targetKey plan.target) then return none

  -- The hop needs a connection of its own when it leaves this origin, and equally when the
  -- redirect response ended the connection it arrived on. Only a `.follow` policy can open one, so
  -- a standalone agent hands the 3xx back instead of writing to a connection that is going away.
  if plan.isCrossOrigin ∨ ¬allowsConnectionReuse config response.line then
    if let .stop := agent.crossOrigin then return none

  return some plan

/--
Points the agent at the connection the next hop must use: the current one when the hop stays on
this origin and the redirect response left it usable, otherwise a fresh one from the `.follow`
policy, with the outgoing connection released first.
-/
private def advanceAgent (agent : Agent) (config : Config) (plan : RedirectPlan)
    (response : Response Body.Stream) : Async (Except Error Agent) := do
  if !plan.isCrossOrigin ∧ allowsConnectionReuse config response.line then
    -- The connection can still have died since the response arrived; falling through re-acquires.
    if !(← agent.connection.isClosed) then return .ok agent

  let .follow acquire := agent.crossOrigin
    | return .ok agent

  agent.release agent.connection agent.origin
  match ← acquire plan.origin with
  | .error e => return .error e
  | .ok newConnection =>
    return .ok { agent with connection := newConnection, origin := plan.origin }

private partial def sendWithRedirects
    (agent : Agent) (request : Request Body.Any)
    (remaining : Nat) (overrides : RequestOverrides)
    (history : Array (URI.Origin × String) := #[]) :
    Async (Except Error (Response Body.Stream)) := do

  -- Recomputed per hop: a cross-origin swap may land on a connection with a different `Config`.
  let config := overrides.apply agent.connection.config
  let history := history.push (agent.origin, targetKey request.line.uri)
  let request := withHostHeader agent (rewriteForProxy agent request)

  match ← dispatchHop agent request overrides with
  | .error e => return .error e
  | .ok (response, completion) =>
    match evaluateRedirect agent config request response remaining history with
    | none => return .ok response
    | some plan =>
      -- Draining the redirect body and rebuilding the request run user-supplied `Body` code;
      -- an exception thrown there must still hand the checked-out connection to `release`.
      let drainLimit := config.redirectBodyDrainLimit.toUInt64
      let next : Except Error (Agent × Request Body.Any) ←
        try
          response.body.drain (drainLimit := some drainLimit)
            (closeStream := response.body.close)
          -- Whether the connection carries the next hop is the connection's decision, not one the
          -- response head can be read for: `maxRequestsPerConnection` and a peer that goes away
          -- after answering are both invisible there. Waiting for the exchange to be reported
          -- finished is what makes `advanceAgent`'s check see the outcome rather than race it.
          if let some completion := completion then
            discard <| await completion.result!
          let newRequest ← buildRedirectRequest plan request
          match ← advanceAgent agent config plan response with
          | .error e => pure (.error e)
          | .ok agent => pure (.ok (agent, newRequest))
        catch err =>
          agent.release agent.connection agent.origin
          pure (.error (.io err))
      match next with
      | .error e => return .error e
      | .ok (agent, newRequest) =>
        sendWithRedirects agent newRequest (remaining - 1) overrides history

end Agent.Impl

namespace Agent

/--
Creates an `Agent` from an already-connected transport `socket`.
-/
def ofTransport [Transport α] (socket : α) (origin : URI.Origin)
    (config : Config := {}) : Async Agent := do
  let connection ← Connection.new socket config
  pure { connection, origin }

/--
Sends a request, automatically following redirects up to the effective `maxRedirects` hops,
returning the response or the typed `Error` that ended the exchange. Middlewares are applied
around every hop. Connection cleanup is handled internally: any failed hop hands its connection
to `agent.release`.
-/
def trySend (agent : Agent) (request : Request Body.Any)
    (overrides : RequestOverrides := {}) : Async (Except Error (Response Body.Stream)) :=
  let config := overrides.apply agent.connection.config
  Agent.Impl.sendWithRedirects agent request config.maxRedirects overrides

/--
Sends a request, automatically following redirects up to the effective `maxRedirects` hops.
Middlewares are applied around every hop.
Use `trySend` to receive failures as a typed `Error` instead of a thrown exception.
-/
def send {β : Type} [Coe β Body.Any] (agent : Agent) (request : Request β)
    (overrides : RequestOverrides := {}) : Async (Response Body.Stream) :=
  agent.trySend { request with } overrides >>= Error.throwOrPure

end Std.Http.Client.Agent
