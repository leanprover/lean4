/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Http.Client.Session
public import Std.Http.Protocol.H1.Redirect
import Init.Data.Array

public section

/-!
# Agent

A transport-agnostic HTTP user-agent that wraps a `Session` and adds automatic redirect
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
  pool) a session to each new origin.
  -/
  | follow (acquire : URI.Origin → Async (Except Error Session))

/--
An HTTP user-agent that manages a connection to a host and follows redirects.

The agent owns its session's lifecycle: any hop that fails, any cross-origin
swap, and any connection error after a delivered response hands the session to
`release` exactly once.
-/
structure Agent where
  /--
  The underlying HTTP session.
  -/
  session : Session

  /--
  The origin (scheme, host, port) this agent is currently connected to.
  -/
  origin : URI.Origin

  /--
  Returns a session the agent is done with: one that broke during a hop or was
  swapped out for a cross-origin redirect. A pool reclaims sessions here; the
  default closes the session.
  -/
  release : Session → URI.Origin → Async Unit := fun session _ => session.close

  /--
  Policy for cross-origin redirects. With `.stop` (the default) they end the
  redirect chain and the 3xx response is returned as-is; a pool supplies
  `.follow` with its session acquisition so the chain continues on a fresh
  session.
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
    let query := af.query
    { request with line := { request.line with uri := .originForm af.path query } }
  | _ => request

private def rewriteForProxy (agent : Agent) (request : Request Body.Any) : Request Body.Any :=
  if agent.session.config.proxy.isSome then
    toAbsoluteForm request agent.origin.scheme agent.origin.host agent.origin.port
  else
    toOriginForm request

/--
Performs one request/response hop through the middleware chain. Failures flow through the
chain as a typed `Except Client.Error`; an exception thrown by a middleware itself is wrapped
as `Client.Error.io`.

Session cleanup is owned entirely by this function: on a failed hop the session is handed to
`agent.release` exactly once, and on a successful hop a background task watches the exchange
completion and releases the session if the connection errors after the response was delivered.
The completion promise of the innermost send is captured in a ref because middlewares only see
the response: a hop that short-circuits without sending has no completion to watch.
-/
private def dispatchHop (agent : Agent) (request : Request Body.Any)
    (timeout? : Option Timeout) : Async (Except Client.Error (Response Body.Stream)) := do
  let completionRef ← IO.mkRef (none : Option (IO.Promise (Except Client.Error Unit)))
  let inner : Request Body.Any → Async (Except Client.Error (Response Body.Stream)) := fun req => do
    match ← agent.session.sendTracked req timeout? with
    | .ok (response, completion) =>
      completionRef.set (some completion)
      return .ok response
    | .error e => return .error e
  let chain := agent.middlewares.foldr (fun mw next req => mw req next) inner
  match ← try chain request catch err => pure (.error (.io err)) with
  | .ok response =>
    if let some completion ← completionRef.get then
      background do
        if let .error _ ← await completion.result! then
          agent.release agent.session agent.origin
    return .ok response
  | .error e =>
    agent.release agent.session agent.origin
    return .error e

private inductive RedirectStep where
  | final
  | stop
  | follow (plan : RedirectPlan)

/--
Canonical string key for a request target used by cycle detection. The origin is tracked
separately in the history tuple, so this drops the authority and keys only on the path and query.
Both origin-form and absolute-form targets normalize to the same string so that a redirect chain
that alternates between direct (origin-form) and cross-origin (absolute-form) hops is still detected
as a cycle.
-/
private def targetKey : RequestTarget → String
  | .absoluteForm af =>
    toString (RequestTarget.originForm af.path (af.query))
  | t => toString t

private def evaluateRedirect
    (agent : Agent) (request : Request Body.Any)
    (response : Response Body.Stream) (remaining : Nat)
    (history : Array (URI.Origin × String)) : RedirectStep := Id.run do

  if remaining = 0 then
    .final
  else
    let decide :=
      decideRedirect agent.origin
        request.line request.body.reset?.isSome agent.session.config.onlySafeRedirects
          response.line.version response.line.status response.line.headers

    match decide with
    | .done => return .final
    | .follow plan =>

      -- Gate 1: cycle detection.
      let nextKey := (plan.origin, targetKey plan.target)

      if history.contains nextKey then
        return .stop

      -- Gate 2: cross-origin redirects need a `.follow` policy.
      if plan.isCrossOrigin then
        if let .stop := agent.crossOrigin then
          return .stop

      return .follow plan

/--
Swaps the agent to the redirect target's origin: releases the outgoing session and acquires
one for the new origin via the `.follow` policy. Same-origin hops keep the agent unchanged.
-/
private def advanceAgent (agent : Agent) (plan : RedirectPlan) : Async (Except Client.Error Agent) := do
  if !plan.isCrossOrigin then return .ok agent

  let .follow acquire := agent.crossOrigin
    | return .ok agent

  agent.release agent.session agent.origin
  match ← acquire plan.origin with
  | .error e => return .error e
  | .ok newSession => return .ok { agent with session := newSession, origin := plan.origin }

private partial def sendWithRedirects
    (agent : Agent) (request : Request Body.Any)
    (remaining : Nat) (timeout? : Option Timeout)
    (history : Array (URI.Origin × String) := #[]) : Async (Except Client.Error (Response Body.Stream)) := do

  let history := history.push (agent.origin, targetKey request.line.uri)
  let request := rewriteForProxy agent request

  match ← dispatchHop agent request timeout? with
  | .error e => return .error e
  | .ok response =>
    match evaluateRedirect agent request response remaining history with
    | .final | .stop =>
      return .ok response
    | .follow plan =>
      -- Draining the redirect body and rebuilding the request run user-supplied `Body` code;
      -- an exception thrown there must still hand the checked-out session to `release`.
      let next : Except Client.Error (Agent × Request Body.Any) ←
        try
          response.body.drain (drainLimit := some agent.session.config.redirectBodyDrainLimit.toUInt64)
            (closeStream := response.body.close)
          let newRequest ← buildRedirectRequest plan request
          match ← advanceAgent agent plan with
          | .error e => pure (.error e)
          | .ok agent => pure (.ok (agent, newRequest))
        catch err =>
          agent.release agent.session agent.origin
          pure (.error (.io err))
      match next with
      | .error e => return .error e
      | .ok (agent, newRequest) =>
        sendWithRedirects agent newRequest (remaining - 1) timeout? history

end Agent.Impl

namespace Agent

/--
Creates an `Agent` from an already-connected transport `socket`.
-/
def ofTransport [Transport α] (socket : α) (origin : URI.Origin)
    (config : Config := {}) : Async Agent := do
  let session ← Session.new socket config
  pure { session, origin }

/--
Sends a request, automatically following redirects up to `config.maxRedirects` hops
(or `overrides.maxRedirects` when set), returning the response or the typed `Error`
that ended the exchange. Middlewares are applied around every hop. Session cleanup
is handled internally: any failed hop hands its session to `agent.release`.
-/
def trySend (agent : Agent) (request : Request Body.Any)
    (overrides : RequestOverrides := {}) : Async (Except Client.Error (Response Body.Stream)) :=
  Agent.Impl.sendWithRedirects agent request
    (overrides.maxRedirects.getD agent.session.config.maxRedirects) overrides.timeout

/--
Sends a request, automatically following redirects up to `config.maxRedirects` hops
(or `overrides.maxRedirects` when set). Middlewares are applied around every hop.
Use `trySend` to receive failures as a typed `Error` instead of a thrown exception.
-/
def send {β : Type} [Coe β Body.Any] (agent : Agent) (request : Request β)
    (overrides : RequestOverrides := {}) : Async (Response Body.Stream) :=
  agent.trySend { request with } overrides >>= Client.Error.throwOrPure

end Std.Http.Client.Agent
