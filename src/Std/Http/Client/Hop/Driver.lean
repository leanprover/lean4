/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Http.Client.Config
public import Std.Http.Client.Error
public import Std.Http.Protocol.H1.Redirect

public section

/-!
# Hop driver

The decisions of one request a client sends, across the hops it takes, without I/O. Each hop is one
exchange on a connection to one origin. The driver decides whether a response is the caller's or a
redirect to follow (RFC 9110 §15.4, through `decideRedirect`), how the next hop's request is built,
whether a failed hop is retried on a fresh connection, and what becomes of the request body on each
hop.

The client is the driver's interpreter. It performs the `Command`s that `step` returns, in order,
and reports what happened as the next `Input`:
- After `send`, the next input is `responded` with the hop's response head, or `failed`.
- After `drain`, the next input is `drained`, once the response body was read to its end or given up.
- After `wait`, the next input is `waited`, once that many milliseconds passed.
- After `deliver` or `fail`, the request is over and nothing follows.

A hop holds its connection from `send` until the driver passes it on: `release` gives it back to
the pool, reusable or not, and `deliver` hands it over with the response, to go back once its
exchange ends. A hop that `failed` gives its connection up: the interpreter closes it.
-/

namespace Std.Http.Client

set_option linter.all true

open Std Http Protocol H1

namespace Hop.Driver

/--
When a request is sent again: the statuses of final responses that are retried, and the delays
between attempts, in milliseconds.
-/
structure Retry where
  /-- Final responses with these statuses are retried, like connection-level failures. -/
  statuses : Array Status := #[]
  /-- The delay before the first retry, doubled for each further one. -/
  delay : Nat := 0
  /-- The longest delay, whatever the doubling or the response's `Retry-After` asks for. -/
  maxDelay : Nat := 30000

/--
The delay before retry `n` (the first is `1`): `retryAfter` milliseconds when the response named
them, and the doubled delay otherwise, both at most `maxDelay`.
-/
def Retry.delayFor (r : Retry) (n : Nat) (retryAfter : Option Nat := none) : Nat :=
  (retryAfter.getD (r.delay * 2 ^ (n - 1))).min r.maxDelay

/--
The delay a response's `Retry-After` names, in milliseconds, when it is given in seconds
(RFC 9110 §10.2.3). A date is not read: the driver has no wall clock.
-/
def retryAfter? (head : Response.Head) : Option Nat :=
  (head.headers.get? (.mk "retry-after")).bind fun v => (v.value.trimAscii.toString.toNat?).map (· * 1000)

/--
The request body a hop sends.
-/
inductive BodySource where
  /-- The caller's body as it stands: the first hop of the first attempt. -/
  | original
  /-- The caller's body, rewound first: a redirect that resends it, or a retry. -/
  | rewound
  /-- No content: a redirect that turned the request into a `GET`, or one that has none. -/
  | empty
deriving Repr, BEq

/--
What the interpreter reports to the driver.
-/
inductive Input where
  /-- Starts the request. -/
  | start
  /-- The hop got a final response, with this head. -/
  | responded (head : Response.Head)
  /--
  The hop failed with `err`. `clientClosed` reports that the client was closed since the request
  started, which rules out a retry.
  -/
  | failed (err : Client.Error) (clientClosed : Bool)
  /--
  The body of a redirect response was read to its end, with whether its connection can carry
  another request; or reading it failed with the hop's error.
  -/
  | drained (result : Except Client.Error Bool)
  /-- The delay `wait` asked for passed. -/
  | waited

/--
What the driver asks the interpreter to do, in order.
-/
inductive Command where
  /--
  Send `head` to `origin` with `body`, on a connection from the pool: a `fresh` one when the request
  is a retry, whose idle connections may have gone stale the same way.
  -/
  | send (origin : URI.Origin) (head : Request.Head) (body : BodySource) (fresh : Bool)
  /-- Read the body of the hop's response to its end, within `intermediateBodyDrainLimit`. -/
  | drain
  /-- Wait `ms` milliseconds before the next attempt. -/
  | wait (ms : Nat)
  /-- Give the hop's connection back to the pool, to carry another request when `reusable`. -/
  | release (reusable : Bool)
  /-- Hand the hop's response to the caller; its connection goes back once its exchange ends. -/
  | deliver
  /-- Fail the request with `err`. -/
  | fail (err : Client.Error)
deriving Inhabited

/--
What the driver waits for.
-/
inductive Stage where
  /-- `start`. -/
  | idle
  /-- The response to the hop in flight. -/
  | sending
  /-- The end of a redirect response's body, before the hop that follows `plan`. -/
  | draining (plan : RedirectPlan)
  /-- The end of the body of a response that is retried, before waiting `delay` milliseconds. -/
  | drainingRetry (delay : Nat)
  /-- The end of a delay, before sending `head` to `origin` with `body`. -/
  | waiting (origin : URI.Origin) (head : Request.Head) (body : BodySource)
  /-- Nothing: the request was delivered or failed. -/
  | done

/--
The state of one request across its hops and attempts.
-/
structure State where
  /-- The origin the caller addressed. -/
  initialOrigin : URI.Origin
  /-- The request the caller sent, which a retry sends again. -/
  initialHead : Request.Head
  /-- The caller's body can be rewound. -/
  replayable : Bool
  /-- The origin of the hop in flight. -/
  origin : URI.Origin
  /-- The request of the hop in flight. -/
  head : Request.Head
  /-- The body of the hop in flight can be rewound, which a redirect that resends it needs. -/
  hopReplayable : Bool
  /-- Redirects still allowed in this attempt. -/
  redirectsLeft : Nat
  /-- The redirects allowed in an attempt. -/
  maxRedirects : Nat
  /-- The attempts made, the one in flight included. -/
  attempts : Nat := 1
  /-- The attempts allowed: one and the retries. -/
  maxAttempts : Nat
  /-- Every hop of this attempt so far, as origin, method and target, to stop a redirect cycle. -/
  history : Array (URI.Origin × Method × String) := #[]
  /-- A hop of this attempt got a response: the request, or one it was redirected from, reached a peer. -/
  answered : Bool := false
  /-- What the driver waits for. -/
  stage : Stage := .idle
  /-- The body the hop in flight was sent with: a retry of it sends the same, rewound. -/
  body : BodySource := .original
  /-- When the request is sent again. -/
  retry : Retry := {}
  /-- Which redirects are followed, of those `decideRedirect` allows. -/
  policy : RedirectPolicy := fun _ _ _ _ => true

/--
The key a hop's target is remembered by for cycle detection: its path and query, the origin being
kept apart, so origin-form and absolute-form targets of one resource match.
-/
def targetKey : RequestTarget → String
  | .absoluteForm af => toString (RequestTarget.originForm af.path af.query)
  | t => toString t

/--
The state of a request to `origin` with head `head`, whose body can be rewound when `replayable`,
allowed `maxRedirects` redirects per attempt and `maxRetries` retries.
-/
def init (origin : URI.Origin) (head : Request.Head) (replayable : Bool) (maxRedirects : Nat)
    (maxRetries : Nat) (retry : Retry := {}) (policy : RedirectPolicy := fun _ _ _ _ => true) :
    State :=
  { initialOrigin := origin, initialHead := head, replayable, origin, head
    hopReplayable := replayable, redirectsLeft := maxRedirects, maxRedirects
    maxAttempts := maxRetries + 1, retry, policy }

/--
Starts a hop to `origin` with `head`.
-/
private def sendHop (s : State) (origin : URI.Origin) (head : Request.Head) (body : BodySource) :
    State × Array Command :=
  ({ s with
      origin, head, body
      history := s.history.push (origin, head.method, targetKey head.uri)
      stage := .sending },
    #[.send origin head body (s.attempts > 1)])

/--
The redirect `head` asks for, if it is one to follow: the attempt has redirects left, the response
names one target, `decideRedirect` follows it, and the chain has not already sent the same method to
the same target. The method is part of what was visited, so a `POST` answered with `303` to its own
URL is followed with `GET`.
-/
def redirectOf (s : State) (head : Response.Head) : Option RedirectPlan := Id.run do
  if s.redirectsLeft = 0 then return none
  -- Several `Location` fields name no single target; picking one would be a guess.
  if ((head.headers.getAll? .location).map (·.size)).getD 0 > 1 then return none
  let .follow plan := decideRedirect s.origin s.head s.hopReplayable head.status head.headers
    | return none
  if s.history.contains (plan.origin, plan.method, targetKey plan.target) then return none
  if !s.policy s.origin s.head head.status plan then return none
  return some plan

/--
The request of the hop that follows `plan`. A request that loses its content also loses
`Expect: 100-continue`, which RFC 9110 §10.1.1 forbids without content.
-/
def nextHead (s : State) (plan : RedirectPlan) : Request.Head :=
  let headers := match plan.bodyAction with
    | .empty => plan.headers.erase .expect
    | .replay => plan.headers
  { s.head with uri := plan.target, method := plan.method, headers }

/--
Whether a request that failed with `err` may be sent again: the failure is one a fresh connection
may not repeat, and the request either can be replayed whole (an idempotent method and a body that
rewinds) or provably never reached a peer.
-/
def mayRetry (s : State) (err : Client.Error) (clientClosed : Bool) : Bool :=
  let resendable :=
    (s.initialHead.method.isIdempotent && s.replayable) || (err.isNeverSent && !s.answered)
  err.isRetryable && resendable && s.attempts < s.maxAttempts && !clientClosed

/--
Whether a final response with `head` is retried: its status is one the client retries, the hop can
be sent again whole (an idempotent method and a body that rewinds), and an attempt is left.
-/
def retriesStatus (s : State) (head : Response.Head) : Bool :=
  s.retry.statuses.contains head.status && s.head.method.isIdempotent && s.hopReplayable &&
    s.attempts < s.maxAttempts

/--
Sends `head` to `origin` once `delay` milliseconds passed: at once when it is `0`.
-/
private def sendAfter (s : State) (delay : Nat) (origin : URI.Origin) (head : Request.Head)
    (body : BodySource) : State × Array Command :=
  if delay == 0 then sendHop s origin head body
  else ({ s with stage := .waiting origin head body }, #[.wait delay])

/--
Answers an input: returns the new state and the commands to perform, in order.
-/
def step (s : State) (input : Input) : State × Array Command :=
  match s.stage, input with
  | .idle, .start =>
    -- An absolute-form target names its own origin. Sent to another, through a proxy it would reach
    -- the target's host carrying the cookies and credentials of the origin addressed.
    match s.head.uri with
    | .absoluteForm uri =>
      if uri.origin? != some s.origin then
        ({ s with stage := .done }, #[.fail (.invalidRequest
          s!"request target {s.head.uri} does not belong to the origin it is sent to, {s.origin}")])
      else sendHop s s.origin s.head .original
    | _ => sendHop s s.origin s.head .original
  | .sending, .responded head =>
    let s := { s with answered := true }
    match redirectOf s head with
    | some plan => ({ s with stage := .draining plan }, #[.drain])
    | none =>
      if retriesStatus s head then
        ({ s with stage := .drainingRetry (s.retry.delayFor s.attempts (retryAfter? head)) }, #[.drain])
      else ({ s with stage := .done }, #[.deliver])
  | .sending, .failed err clientClosed =>
    if mayRetry s err clientClosed then
      let delay := s.retry.delayFor s.attempts
      let s := { s with
        attempts := s.attempts + 1, history := #[], answered := false
        redirectsLeft := s.maxRedirects, hopReplayable := s.replayable }
      sendAfter s delay s.initialOrigin s.initialHead (if s.replayable then .rewound else .original)
    else ({ s with stage := .done }, #[.fail err])
  | .draining plan, .drained (.ok reusable) =>
    let (body, hopReplayable) := match plan.bodyAction with
      -- An empty body rewinds, so a challenge on the next hop can still be answered.
      | .empty => (BodySource.empty, true)
      | .replay => (BodySource.rewound, s.hopReplayable)
    let s := { s with redirectsLeft := s.redirectsLeft - 1, hopReplayable }
    let (s, cmds) := sendHop s plan.origin (nextHead s plan) body
    (s, #[Command.release reusable] ++ cmds)
  | .draining _, .drained (.error err) =>
    ({ s with stage := .done }, #[.release false, .fail err])
  | .drainingRetry delay, .drained result =>
    -- The response is retried whether or not its body could be read: only the connection differs.
    let reusable := match result with | .ok reusable => reusable | .error _ => false
    let body := if s.body == .empty then BodySource.empty else .rewound
    let (s, cmds) := sendAfter { s with attempts := s.attempts + 1 } delay s.origin s.head body
    (s, #[Command.release reusable] ++ cmds)
  | .waiting origin head body, .waited => sendHop s origin head body
  | _, _ => (s, #[])

end Hop.Driver

end Std.Http.Client
