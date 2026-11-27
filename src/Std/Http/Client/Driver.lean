/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init.Data.Hashable
public import Std.Data.HashMap
public import Std.Http.Client.Connection.Driver
public import Std.Http.Client.Pool.Driver
public import Std.Http.Client.Hop.Driver
public import Std.Http.Client.Authenticator

public section

/-!
# Client driver

The decisions of an HTTP client, without I/O: one machine made of the drivers of its parts. For each
request it runs a hop driver (redirects and retries), for the pool a pool driver (which connection
each hop gets), and for each connection a connection driver (one exchange after another). The
machine routes what each part decides to the part it concerns, so the only commands left for the
interpreter are real effects: socket reads and writes, opening a connection, and what the caller of
each request sees.

The interpreter names each request with a `Ticket` and reports what happened as the next `Input`;
the machine names each connection when it asks for it to be opened. Its contract:
- A connection is reported only what it asked for: `received` after `recv`, `written` after a write
  command, a fired timer that `wants` armed, a request body chunk or body interest for a request
  `wants` lists.
- After `close` for a connection, nothing more is reported for it.
- `loadCookies` is answered with `cookies`, and `authenticate` with `credential`, for that request.

The machine reads some response bodies itself, without the caller: the body of a redirect it
follows, which it discards, and the body of an authentication challenge it answers, which it keeps
in case the challenge goes to the caller after all. Both stop at `intermediateBodyDrainLimit`.

Parts never step each other directly: what another part asks of a connection (a request to send,
its response body to drain, its cancellation) is recorded on the connection and delivered once it
waits on its sources, so a connection is never handed an input in a stage that would drop it.
-/

namespace Std.Http.Client.Driver

set_option linter.all true

open Std Http Protocol Internal

/-- Names a request. The interpreter chooses it, unique among the requests not yet answered. -/
abbrev Ticket := Pool.Driver.Ticket

/-- Names a connection. The machine chooses it when it asks for the connection to be opened. -/
abbrev ConnectionId := Pool.Driver.ConnectionId

/-! ## Interface -/

/-- What the caller of a request does, reported by the interpreter. -/
inductive RequestInput where
  /-- The request body returned a chunk, or `none` at its end. -/
  | pulled (chunk : Option Chunk)
  /-- The request body failed. -/
  | pullFailed (err : IO.Error)
  /-- The caller waits for more of the response body (`true`), or closed it (`false`). -/
  | bodyInterest (wanted : Bool)

/-- What happened, reported by the interpreter. -/
inductive Input where
  /--
  A caller sends a request to `origin` with head `head` and a body of length `size` when known,
  which can be rewound when `replayable`.
  -/
  | submit (ticket : Ticket) (origin : URI.Origin) (head : Request.Head) (size : Option Body.Length)
      (overrides : RequestOverrides) (replayable : Bool)
  /-- The caller of request `ticket` acted on its bodies. -/
  | request (ticket : Ticket) (input : RequestInput)
  /-- Connection `id` reported `input`: bytes, writes completed, a timer, a failure. -/
  | connection (id : ConnectionId) (input : Connection.Driver.Input)
  /-- Opening connection `id` ended, with the error that failed it. -/
  | dialed (id : ConnectionId) (result : Except Client.Error Unit)
  /-- The cookie handler's cookies for the hop of request `ticket`, after `loadCookies`. -/
  | cookies (ticket : Ticket) (values : Array Header.Value)
  /-- The authenticator's answer to the challenge of request `ticket`, after `authenticate`. -/
  | credential (ticket : Ticket) (value : Option Header.Value)
  /-- The client closes. -/
  | close
  /-- Nothing happened: the machine asked to step again, through `Wants.resume`. -/
  | resume
  /-- The response of request `ticket` is overdue: the time `Wants.deadline` named passed. -/
  | expired (ticket : Ticket)
  /--
  Request `ticket` fails with `err`, wherever it is, and is not retried: its caller abandoned it, or
  what the interpreter does for it (rewinding its body, loading its cookies) failed.
  -/
  | cancel (ticket : Ticket) (err : Client.Error)
  /-- The interceptor's request for the hop of request `ticket`, or its failure, after `intercept`. -/
  | intercepted (ticket : Ticket) (result : Except Client.Error Request.Head)
  /-- The delay before the next attempt of request `ticket` passed: the time `Wants.retry` named. -/
  | retryDue (ticket : Ticket)

/-- What the interpreter does with a connection. -/
inductive ConnectionCommand where
  /-- Hand `data` to the connection's writes; report `written`. -/
  | write (data : ChunkedBuffer)
  /-- Wait until every write handed over completed; report `written`. -/
  | awaitWritten
  /-- Wait until the writes in flight complete; report `written`. -/
  | flush
  /-- Close the socket. Nothing more is reported for the connection. -/
  | close

/-- What the interpreter does for the caller of a request. -/
inductive RequestCommand where
  /-- Send this hop's request body from `source`: the caller's, rewound, or none. -/
  | body (source : Hop.Driver.BodySource)
  /-- Give the caller the response head, with the length of its body when known. -/
  | respond (head : Response.Head) (size : Option Body.Length)
  /-- Offer `chunk` to the response body, which ends after it with `final`. -/
  | offerBody (chunk : Chunk) (final : Bool)
  /-- Close the response body: the caller has all of it. -/
  | endResponse
  /-- Close the request body: it was sent, or it is not wanted anymore. -/
  | closeRequestBody
  /-- The request is over: close what is still open of its bodies. -/
  | complete
  /-- The request failed with `err`; fail its response body if it is open. -/
  | fail (err : Client.Error)
  /-- Ask the cookie handler for its cookies for `target` at `origin`; report `cookies`. -/
  | loadCookies (origin : URI.Origin) (target : RequestTarget)
  /-- Hand the header fields of a response to `target` at `origin` to the cookie handler. -/
  | storeCookies (origin : URI.Origin) (target : RequestTarget) (headers : Headers)
  /-- Ask the authenticator to answer `challenge`; report `credential`. -/
  | authenticate (challenge : Challenge)
  /-- Run the interceptor's `onRequest` on the hop's request to `origin`; report `intercepted`. -/
  | intercept (origin : URI.Origin) (head : Request.Head)
  /-- Run the interceptor's `onResponse` on the final response head of the hop to `origin`. -/
  | observe (origin : URI.Origin) (request : Request.Head) (head : Response.Head)
  /-- Hand the caller the trailer fields of the response body; they come before its end. -/
  | trailers (fields : Headers)
  /-- Run the interceptor's `onInformational` on an informational response to the hop to `origin`. -/
  | informational (origin : URI.Origin) (request : Request.Head) (head : Response.Head)

/-- What the machine asks the interpreter to do, in order. -/
inductive Command where
  /-- Open connection `id` to `origin`, then report `dialed id`. -/
  | dial (id : ConnectionId) (origin : URI.Origin)
  /-- Act on connection `id`. -/
  | connection (id : ConnectionId) (command : ConnectionCommand)
  /-- Act for the caller of request `ticket`. -/
  | request (ticket : Ticket) (command : RequestCommand)

/-! ## State -/

/-- A connection: its driver, and what the other parts asked of it. -/
structure Conn where
  /-- The origin it was opened for. -/
  origin : URI.Origin
  /-- Its driver. -/
  driver : Connection.Driver.State
  /-- The request it carries. -/
  ticket : Option Ticket := none
  /-- The request's head was handed to the driver. -/
  submitted : Bool := false
  /--
  The machine reads the response body itself, with the bytes it may still take, keeping them when
  `keep`: a redirect's body (discarded) or a challenge's (kept).
  -/
  consume : Option (Nat × Bool) := none
  /-- The pool asked to close it. -/
  cancel : Bool := false
  /-- Its last write was empty, so the machine reports it `written` itself. -/
  owedWritten : Bool := false
  /-- When its driver last stepped: the start of the waits it arms `within` a timeout. -/
  since : Nat := 0

/-- A request: its hop driver, and the hop in flight. -/
structure Req where
  /-- Its hop driver. -/
  hop : Hop.Driver.State
  /-- The length of the caller's body, when known. -/
  size : Option Body.Length
  /-- Overrides on the client's configuration. -/
  overrides : RequestOverrides
  /-- The hop waiting for a connection, with its body. -/
  send : Option (Request.Head × Hop.Driver.BodySource) := none
  /-- The connection the hop in flight was given. -/
  connection : Option ConnectionId := none
  /-- The hop's response head, with the length of its body. -/
  response : Option (Response.Head × Option Body.Length) := none
  /-- The response went to the caller. -/
  delivered : Bool := false
  /-- The cookies for the hop waiting for a connection, once loaded, when a cookie handler is set. -/
  cookies : Option (Array Header.Value) := none
  /-- The hop waiting for a connection may go: its cookies are loaded, or there is no handler. -/
  cookiesReady : Bool := true
  /-- The request already answered a challenge: a second one goes to the caller. -/
  authTried : Bool := false
  /-- The challenge being answered, with its credential header, once the authenticator replied. -/
  credential : Option (Option Header.Value) := none
  /-- The challenge's body ended, with whether its connection can carry the authenticated retry. -/
  challengeDone : Option Bool := none
  /-- The body kept from a challenge, delivered to the caller if the challenge goes unanswered. -/
  captured : Option ByteArray := none
  /-- The kind of the challenge being answered. -/
  challengeKind : Option Challenge.Kind := none
  /--
  The challenge answered, with the body kept from it, while the authenticated retry has no response:
  delivered instead if the retry fails in a way a new connection might not.
  -/
  fallback : Option (Response.Head × ByteArray) := none
  /-- When its response is overdue: `responseTimeout` after it was submitted. -/
  deadline : Nat := 0
  /-- `State.closes` when it was submitted: a `close` since then rules out its retries. -/
  closes : Nat := 0
  /-- The request the interceptor made of the hop waiting for a connection, once it replied. -/
  intercepted : Option Request.Head := none
  /-- The hop waiting for a connection may go as far as the interceptor goes: it replied, or there
  is none. -/
  interceptReady : Bool := true
  /-- When the next attempt goes, after a delay the hop driver asked for. -/
  retryAt : Option Nat := none

/-- The state of the client. -/
structure State where
  /-- The pool driver. -/
  pool : Pool.Driver.State := { nextId := 1 }
  /-- The connections, by name. -/
  conns : Std.HashMap ConnectionId Conn := {}
  /-- The requests not yet answered, by ticket. -/
  reqs : Std.HashMap Ticket Req := {}
  /-- The retries a request is allowed. -/
  maxRetries : Nat := 1
  /-- How many times the client was closed. -/
  closes : Nat := 0
  /-- Delays the hop drivers asked for in this step, in milliseconds, made absolute at its end. -/
  waits : Array (Ticket × Nat) := #[]

/-! ## Routing -/

/-- What one routing action produces: the new state and the commands for the interpreter. -/
private abbrev Out := State × Array Command

@[inline] private def modifyReq (s : State) (t : Ticket) (f : Req → Req) : State :=
  { s with reqs := s.reqs.modify t f }

@[inline] private def modifyConn (s : State) (id : ConnectionId) (f : Conn → Conn) : State :=
  { s with conns := s.conns.modify id f }

/-- Unbinds connection `id` from its request. -/
@[inline] private def unbind (s : State) (id : ConnectionId) : State :=
  modifyConn s id ({ · with ticket := none, submitted := false, consume := none })

/-- The client was closed since request `t` was submitted: its retries and further hops are ruled out. -/
@[inline] private def closedSince (s : State) (t : Ticket) : Bool :=
  s.reqs[t]?.any (·.closes != s.closes)

/-- An input for a part stepped at once: a request's hop driver, or the pool driver. -/
private inductive Event where
  | hop (t : Ticket) (input : Hop.Driver.Input)
  | pool (input : Pool.Driver.Input)

/--
How deep one input's consequences go between the hop drivers and the pool driver: a pool `reject`
fails a hop, whose retry asks the pool again, which never rejects an `acquire` at once.
-/
private def routeFuel : Nat := 8

/--
Sends the hop of request `t` that waits for a connection: loads its cookies when a handler is set,
runs the interceptor when one is set, and asks the pool for a connection to `origin`.
-/
private def sendHop (cfg : Client.Config) (o : Out) (t : Ticket) (origin : URI.Origin)
    (head : Request.Head) (body : Hop.Driver.BodySource) (fresh : Bool) : Out × Pool.Driver.Input :=
  let (s, out) := o
  let handler := cfg.cookieHandler.isSome
  let intercepts := cfg.interceptor.isSome
  let s := modifyReq s t fun r =>
    { r with
      send := some (head, body), connection := none, response := none, delivered := false
      cookies := none, cookiesReady := !handler, intercepted := none, interceptReady := !intercepts }
  let out := out.push (.request t (.body body))
  let out := if handler then out.push (.request t (.loadCookies origin head.uri)) else out
  let out := if intercepts then out.push (.request t (.intercept origin head)) else out
  ((s, out), .acquire t origin fresh)

/--
Steps the part `event` is for and performs what it decides: the hop and pool drivers at once, and
what concerns a connection recorded on it. `closing` marks the consequences of the client's `close`,
which rule out retries.
-/
private def react (cfg : Client.Config) (closing : Bool) : Nat → Out → Event → Out
  | 0, o, _ => o
  | fuel + 1, (s, out), .pool input =>
    let (pool, cmds) := Pool.Driver.step cfg s.pool input
    cmds.foldl (init := ({ s with pool }, out)) fun (s, out) cmd =>
      match cmd with
      | .dial _ origin id => (s, out.push (.dial id origin))
      | .grant t id =>
        if s.reqs.contains t then
          let s := modifyConn s id ({ · with ticket := some t, submitted := false, consume := none })
          (modifyReq s t ({ · with connection := some id }), out)
        else
          -- The request failed while it waited: the connection goes back unused.
          let reusable := s.conns[id]?.any (·.driver.accepting)
          react cfg closing fuel (s, out) (.pool (.released id reusable))
      | .reject t err =>
        react cfg closing fuel (s, out) (.hop t (.failed err (closing || closedSince s t)))
      | .closeConnection id => (modifyConn s id ({ · with cancel := true }), out)
  | fuel + 1, (s, out), .hop t input =>
    match s.reqs[t]? with
    | none => (s, out)
    | some r =>
      let (hop, cmds) := Hop.Driver.step r.hop input
      cmds.foldl (init := (modifyReq s t ({ · with hop }), out)) fun (s, out) cmd =>
        match cmd with
        | .send origin head body fresh =>
          if closedSince s t then
            react cfg closing fuel (s, out) (.hop t (.failed (.closed "client closed") true))
          else
            let (o, acquire) := sendHop cfg (s, out) t origin head body fresh
            react cfg closing fuel o (.pool acquire)
        | .wait ms => ({ s with waits := s.waits.push (t, ms) }, out)
        | .drain =>
          match s.reqs[t]? |>.bind (·.connection) with
          | some id =>
            (modifyConn s id ({ · with consume := some (cfg.intermediateBodyDrainLimit, false) }), out)
          | none => (s, out)
        -- The connection gives itself back: `complete` releases it, and a failure retires it.
        | .release _ => (s, out)
        | .deliver =>
          match s.reqs[t]? with
          | some { response := some (head, size), captured, .. } =>
            let out := out.push (.request t (.respond head size))
            match captured with
            -- A challenge that went unanswered: its exchange is over, and its body was kept.
            | some body =>
              let out := if body.isEmpty then out else
                out.push (.request t (.offerBody (Chunk.ofByteArray body) true))
              ({ s with reqs := s.reqs.erase t }, out.push (.request t .complete))
            | none => (modifyReq s t ({ · with delivered := true }), out)
          | _ => (s, out)
        | .fail err => ({ s with reqs := s.reqs.erase t }, out.push (.request t (.fail err)))

/--
Settles a challenge once both its body ended and the authenticator replied: sends the request again
with the credential on a connection that can carry it, or hands the challenge to the hop driver,
which delivers it with the body kept.
-/
private def settleChallenge (cfg : Client.Config) (o : Out) (t : Ticket) : Out :=
  let (s, out) := o
  match s.reqs[t]? with
  | some r =>
    match r.challengeDone, r.credential, r.challengeKind, r.response with
    | some reusable, some credential, some kind, some (head, _) =>
      match credential, reusable with
      | some value, true =>
        if closedSince s t then
          react cfg false routeFuel (s, out) (.hop t (.failed (.closed "client closed") true))
        else
        let name := if kind == .server then Header.Name.authorization else .proxyAuthorization
        let retry := { r.hop.head with headers := (r.hop.head.headers.erase name).insert name value }
        let s := modifyReq s t ({ · with
          captured := none, credential := none, challengeDone := none
          fallback := r.captured.map (head, ·) })
        let (o, acquire) := sendHop cfg (s, out) t r.hop.origin retry .rewound false
        react cfg false routeFuel o (.pool acquire)
      | _, _ => react cfg false routeFuel (s, out) (.hop t (.responded head))
    | _, _, _, _ => (s, out)
  | none => (s, out)

/--
A response head for request `t` on connection `c`: hands its fields to the cookie handler, and
either answers its authentication challenge, keeping its body meanwhile, or passes it to the hop
driver.
-/
private def receiveHead (cfg : Client.Config) (o : Out) (id : ConnectionId) (c : Conn) (t : Ticket)
    (driver : Connection.Driver.State) (head : Response.Head) (size : Option Body.Length) : Out :=
  let (s, out) := o
  match s.reqs[t]? with
  | none => (s, out)
  | some r =>
    let out := if cfg.cookieHandler.isSome then
      out.push (.request t (.storeCookies r.hop.origin r.hop.head.uri head.headers)) else out
    let out := if cfg.interceptor.isSome then
      out.push (.request t (.observe r.hop.origin r.hop.head head)) else out
    let s := modifyReq s t ({ · with response := some (head, size), fallback := none })
    let proxy := cfg.proxySelector.select c.origin
    let kind? := Connection.Driver.challengeKind? proxy head.status
    match kind? with
    | some kind =>
      if cfg.authenticator.isSome && !r.authTried && r.hop.hopReplayable && driver.accepting &&
          Connection.Driver.leavesConnectionReusable cfg r.hop.head.method head then
        let challenge : Challenge := {
          kind, origin := c.origin, method := r.hop.head.method, target := r.hop.head.uri
          headers := head.headers, proxy, initialOrigin := r.hop.initialOrigin }
        let s := modifyReq s t ({ · with
          authTried := true, challengeKind := some kind, captured := some .empty
          credential := none, challengeDone := none })
        let s := modifyConn s id ({ · with consume := some (cfg.intermediateBodyDrainLimit, true) })
        (s, out.push (.request t (.authenticate challenge)))
      else react cfg false routeFuel (s, out) (.hop t (.responded head))
    | none => react cfg false routeFuel (s, out) (.hop t (.responded head))

/--
A response body chunk the machine reads itself, for request `t`: discarded or kept, within the
limit. A redirect body over it is given up and its connection closed, and the redirect followed; a
challenge body over it fails the request.
-/
private def consumeChunk (cfg : Client.Config) (o : Out) (id : ConnectionId) (t : Ticket)
    (left : Nat) (keep : Bool) (chunk : Chunk) : Out :=
  let (s, out) := o
  if chunk.data.size ≤ left then
    let s := modifyConn s id ({ · with consume := some (left - chunk.data.size, keep) })
    if keep then (modifyReq s t fun r => { r with captured := r.captured.map (· ++ chunk.data) }, out)
    else (s, out)
  else
    let s := modifyConn (unbind s id) id ({ · with cancel := true })
    if keep then ({ s with reqs := s.reqs.erase t }, out.push (.request t (.fail .bodyLimitExceeded)))
    else react cfg false routeFuel (s, out) (.hop t (.drained (.ok false)))

/--
Hands the caller of request `t` the challenge it answered, with the body kept from it: its
authenticated retry failed on the connection that answered the challenge, which the peer may have
taken back after sending it.
-/
private def deliverFallback (o : Out) (t : Ticket) (head : Response.Head) (body : ByteArray) : Out :=
  let (s, out) := o
  let out := out.push (.request t (.respond head (some (.fixed body.size))))
  let out := if body.isEmpty then out else out.push (.request t (.offerBody (Chunk.ofByteArray body) true))
  ({ s with reqs := s.reqs.erase t }, out.push (.request t .complete))

/--
Performs what the driver of connection `id` decided, in order. `c` is the connection before the step,
and `driver` its driver after it.
-/
private def connCommand (cfg : Client.Config) (id : ConnectionId) (c : Conn)
    (driver : Connection.Driver.State) : Out → Connection.Driver.Command → Out
  | (s, out), .write data =>
    if data.size == 0 then (modifyConn s id ({ · with owedWritten := true }), out)
    else (s, out.push (.connection id (.write data)))
  | (s, out), .awaitWritten => (s, out.push (.connection id .awaitWritten))
  | (s, out), .flush => (s, out.push (.connection id .flush))
  | (s, out), .close =>
    -- A request given the connection but never handed to it never left: it may be sent again.
    let pending := match s.conns[id]? with
      | some c => if c.submitted then none else c.ticket
      | none => none
    let o := ({ s with conns := s.conns.erase id }, out.push (.connection id .close))
    let o := react cfg false routeFuel o (.pool (.connectionClosed id))
    match pending with
    | some t => react cfg false routeFuel o
        (.hop t (.failed (.notSent "connection closed before the request was sent") (closedSince o.1 t)))
    | none => o
  | o, .stopAccepting => react cfg false routeFuel o (.pool (.retired id))
  | (s, out), cmd =>
    -- The binding as it stands now: an earlier command of this batch may have ended it.
    match s.conns[id]? |>.bind (·.ticket) with
    | none => (s, out)
    | some t =>
      let consume := s.conns[id]? |>.bind (·.consume)
      match cmd with
      | .deliverHead head size => receiveHead cfg (s, out) id c t driver head size
      | .trailers fields =>
        if consume.isNone && s.reqs[t]?.any (·.delivered) then
          (s, out.push (.request t (.trailers fields)))
        else (s, out)
      | .interim head =>
        match s.reqs[t]?, cfg.interceptor with
        | some r, some _ => (s, out.push (.request t (.informational r.hop.origin r.hop.head head)))
        | _, _ => (s, out)
      | .offerBody chunk _ =>
        match consume with
        | some (left, keep) => consumeChunk cfg (s, out) id t left keep chunk
        | none =>
          if s.reqs[t]?.any (·.delivered) then (s, out.push (.request t (.offerBody chunk false)))
          else (s, out)
      | .endResponse =>
        if s.reqs[t]?.any (·.delivered) then (s, out.push (.request t .endResponse)) else (s, out)
      | .closeRequestBody => (s, out.push (.request t .closeRequestBody))
      | .complete =>
        let reusable := driver.accepting
        -- Released first, so the hop that follows may get this connection back.
        let o := react cfg false routeFuel (unbind s id, out) (.pool (.released id reusable))
        match consume with
        | some (_, true) =>
          settleChallenge cfg (modifyReq o.1 t ({ · with challengeDone := some reusable }), o.2) t
        | some (_, false) => react cfg false routeFuel o (.hop t (.drained (.ok reusable)))
        | none =>
          if o.1.reqs[t]?.any (·.delivered) then
            ({ o.1 with reqs := o.1.reqs.erase t }, o.2.push (.request t .complete))
          else o
      | .reject err =>
        let s := unbind s id
        match s.reqs[t]? with
        | some r =>
          if r.delivered then ({ s with reqs := s.reqs.erase t }, out.push (.request t (.fail err)))
          else if let some (head, body) := r.fallback.filter (fun _ => err.isRetryable) then
            deliverFallback (s, out) t head body
          else
            match r.hop.stage with
            | .draining _ | .drainingRetry _ =>
              react cfg false routeFuel (s, out) (.hop t (.drained (.error err)))
            | _ => react cfg false routeFuel (s, out) (.hop t (.failed err (closedSince s t)))
        | none => (s, out)
      | .refuse err =>
        let s := unbind s id
        match s.reqs[t]? |>.bind (·.fallback) |>.filter (fun _ => err.isRetryable) with
        | some (head, body) => deliverFallback (s, out) t head body
        | none => react cfg false routeFuel (s, out) (.hop t (.failed err (closedSince s t)))
      | _ => (s, out)

/-- Steps the driver of connection `id` with `input` at `now`, and performs what it decides. -/
private def connStep (cfg : Client.Config) (now : Nat) (o : Out) (id : ConnectionId)
    (input : Connection.Driver.Input) : Out :=
  match o.1.conns[id]? with
  | none => o
  | some c =>
    let (driver, cmds) := Connection.Driver.step cfg c.driver now input
    let s := modifyConn o.1 id ({ · with driver, since := now })
    cmds.foldl (connCommand cfg id c driver) (s, o.2)

/--
The input a connection is owed by the other parts, if it can take one now: `resume` while it runs,
`written` for an empty write, and, once it waits on its sources, its cancellation, the next chunk of
a response body the machine reads itself, or the request it was given.
-/
private def owed (cfg : Client.Config) (s : State) (c : Conn) : Option Connection.Driver.Input :=
  match c.driver.stage with
  | .running => some .resume
  | .writing .. => if c.owedWritten then some (.written true c.driver.writes) else none
  | .polling =>
    if c.cancel then some .cancelled
    else if c.consume.isSome && (Connection.Driver.sources cfg c.driver).responseInterest then
      some (.bodyInterest true)
    else match c.ticket, c.submitted with
      | some t, false =>
        if c.driver.idle then
          match s.reqs[t]? with
          | some r =>
            match r.send, r.cookiesReady && r.interceptReady with
            | some (head, body), true =>
              let head := r.intercepted.getD head
              let proxy := cfg.proxySelector.select c.origin
              let head := { head with
                uri := Connection.Driver.requestTarget proxy c.origin head.uri
                headers := Connection.Driver.requestHeaders c.origin head.headers r.cookies }
              let size := if body == .empty then some (.fixed 0) else r.size
              some (.submit head size r.overrides)
            | _, _ => none
          | none => none
        else none
      | _, _ => none
  | _ => none

/-- Marks on connection `id` that the input `owed` gave it was delivered. -/
private def delivered (s : State) (id : ConnectionId) : Connection.Driver.Input → State
  | .cancelled => modifyConn s id ({ · with cancel := false })
  | .written .. => modifyConn s id ({ · with owedWritten := false })
  | .submit .. => modifyConn s id ({ · with submitted := true })
  | _ => s

/--
Delivers what the connections are owed, until none is owed anything they can take now. `fuel` bounds
the rounds.
-/
private def settle (cfg : Client.Config) (now : Nat) : Nat → Out → Out
  | 0, o => o
  | fuel + 1, (s, out) =>
    let next := s.conns.fold (init := none) fun found id c =>
      match found with
      | some _ => found
      | none => (owed cfg s c).map (id, ·)
    match next with
    | none => (s, out)
    | some (id, input) => settle cfg now fuel (connStep cfg now (delivered s id input, out) id input)

/--
The rounds one `step` gives `settle`: each connection can be owed a few inputs in turn, and a body
the machine reads itself one per chunk it holds. A connection still owed an input after them is
reported by `Wants.resume`.
-/
private def settleFuel (s : State) : Nat := 64 * (s.conns.size + 1)

/-- Some connection is owed an input it can take now. -/
private def owes (cfg : Client.Config) (s : State) : Bool :=
  s.conns.fold (init := false) fun found _ c => found || (owed cfg s c).isSome

@[inline] private def millis (timeout : Client.Timeout) : Nat :=
  timeout.val.toInt.toNat

/--
Fails request `t` with `err`, unless its response already went to the caller. A connection it was
given but never handed its request goes back to the pool; one carrying its exchange is cancelled.
-/
private def abandon (cfg : Client.Config) (s : State) (t : Ticket) (err : Client.Error) : Out :=
  match s.reqs[t]? with
  | some r =>
    if r.delivered then (s, #[]) else
    let o : Out := ({ s with reqs := s.reqs.erase t }, #[.request t (.fail err)])
    match r.connection with
    | some id =>
      match s.conns[id]? with
      | some c =>
        if c.ticket != some t then o
        else if c.submitted then (modifyConn (unbind o.1 id) id ({ · with cancel := true }), o.2)
        else react cfg false routeFuel (unbind o.1 id, o.2) (.pool (.released id c.driver.accepting))
      | none => o
    | none => o
  | none => (s, #[])

/-! ## Stepping -/

/--
Answers an input at time `now`, in milliseconds of a monotonic clock: returns the new state and the
commands to perform, in order.
-/
def step (cfg : Client.Config) (s : State) (now : Nat) (input : Input) : State × Array Command :=
  let o : Out := match input with
    | .submit t origin head size overrides replayable =>
      let rcfg := overrides.apply cfg
      let deadline := now + millis rcfg.responseTimeout
      let retry : Hop.Driver.Retry := {
        statuses := rcfg.retryStatuses, delay := rcfg.retryDelay.toInt.toNat
        maxDelay := rcfg.maxRetryDelay.toInt.toNat }
      let hop := Hop.Driver.init origin head replayable rcfg.maxRedirects s.maxRetries retry
        (rcfg.redirectPolicy.getD fun _ _ _ _ => true)
      let r : Req := { hop, size, overrides, deadline, closes := s.closes }
      react cfg false routeFuel ({ s with reqs := s.reqs.insert t r }, #[]) (.hop t .start)
    | .request t input =>
      match s.reqs[t]? |>.bind (·.connection) with
      | some id =>
        let input : Connection.Driver.Input := match input with
          | .pulled chunk => .pulled chunk
          | .pullFailed err => .pullFailed err
          | .bodyInterest wanted => .bodyInterest wanted
        connStep cfg now (s, #[]) id input
      | none => (s, #[])
    | .connection id input => connStep cfg now (s, #[]) id input
    | .dialed id result =>
      let origin := (s.pool.pools.find? (·.dials.any (·.id == id))).map (·.origin)
      let s := match result, origin with
        | .ok (), some origin =>
          let conn : Conn :=
            { origin, driver := Connection.Driver.init { config := cfg.toH1Config }, since := now }
          { s with conns := s.conns.insert id conn }
        | _, _ => s
      react cfg false routeFuel (s, #[]) (.pool (.dialed id result))
    | .cookies t values =>
      (modifyReq s t ({ · with cookies := some values, cookiesReady := true }), #[])
    | .credential t value =>
      settleChallenge cfg (modifyReq s t ({ · with credential := some value }), #[]) t
    | .close => react cfg true routeFuel ({ s with closes := s.closes + 1 }, #[]) (.pool .close)
    | .resume => (s, #[])
    | .expired t => abandon cfg s t .timeout
    | .cancel t err => abandon cfg s t err
    | .intercepted t (.ok head) =>
      (modifyReq s t ({ · with intercepted := some head, interceptReady := true }), #[])
    | .intercepted t (.error err) => abandon cfg s t err
    | .retryDue t =>
      match s.reqs[t]? with
      | some { retryAt := some _, .. } =>
        react cfg false routeFuel (modifyReq s t ({ · with retryAt := none }), #[]) (.hop t .waited)
      | _ => (s, #[])
  let (s, out) := settle cfg now (settleFuel o.1) o
  -- The delays the hop drivers asked for start now.
  let s := s.waits.foldl (init := { s with waits := #[] }) fun s (t, ms) =>
    modifyReq s t ({ · with retryAt := some (now + ms) })
  (s, out)

/-! ## What the interpreter waits on -/

/-- What the interpreter waits on, across the connections and requests. -/
structure Wants where
  /-- Receive from these connections, at most this many bytes each. -/
  recv : Array (ConnectionId × Nat) := #[]
  /-- Report when the writes of these connections complete. -/
  writesIdle : Array ConnectionId := #[]
  /-- Watch the writes of these connections for a stall. -/
  writesLate : Array ConnectionId := #[]
  /-- Pull the next chunk of these requests' bodies. -/
  requestBody : Array Ticket := #[]
  /-- Report when the callers of these requests wait for more of the response body, or close it. -/
  responseInterest : Array Ticket := #[]
  /-- Report only when the callers of these requests close the response body. -/
  responseClosed : Array Ticket := #[]
  /-- The timer due first, of the connection it belongs to, with the milliseconds until it fires. -/
  timer : Option (ConnectionId × Connection.Driver.Timer × Nat) := none
  /-- The request whose response is due first, with the milliseconds until it is overdue: report
  `expired` then. -/
  deadline : Option (Ticket × Nat) := none
  /-- A connection is owed an input the last step did not deliver: report `resume` at once. -/
  resume : Bool := false
  /-- The request whose next attempt is due first, with the milliseconds until then: report
  `retryDue` then. -/
  retry : Option (Ticket × Nat) := none

/-- What the connections that wait on their sources wait on, at `now`. -/
private def connectionWants (cfg : Client.Config) (s : State) (now : Nat) : Wants :=
  s.conns.fold (init := {}) fun w id c =>
    if !c.driver.waits then w
    else
      let src := Connection.Driver.sources cfg c.driver
      let forTicket (b : Bool) (arr : Array Ticket) :=
        match c.ticket, b with
        | some t, true => arr.push t
        | _, _ => arr
      -- A body the machine reads itself is none of the caller's business.
      let callerReads := c.consume.isNone
      -- A wait armed `within` a timeout started when this connection last stepped, not now: inputs
      -- for other connections do not restart it.
      let due := src.timers.foldl (init := none) fun due (timer, arm) =>
        let ms := match arm with
          | .until deadline => deadline - now
          | .within timeout => (c.since + timeout) - now
        match due with
        | some (_, earliest) => if ms < earliest then some (timer, ms) else due
        | none => some (timer, ms)
      let timer := match w.timer, due with
        | some (i, t, ms), some (t', ms') => if ms' < ms then some (id, t', ms') else some (i, t, ms)
        | none, some (t', ms') => some (id, t', ms')
        | due, none => due
      { recv := match src.recv with | some n => w.recv.push (id, n) | none => w.recv
        writesIdle := if src.writesIdle then w.writesIdle.push id else w.writesIdle
        writesLate := if src.writesLate then w.writesLate.push id else w.writesLate
        requestBody := forTicket src.requestBody w.requestBody
        responseInterest := forTicket (callerReads && src.responseInterest) w.responseInterest
        responseClosed := forTicket (callerReads && src.responseClosed) w.responseClosed
        timer }

/-- What the interpreter waits on at `now`: the sources of every connection that waits on
them, the response due first, and whether to step again at once. -/
def wants (cfg : Client.Config) (s : State) (now : Nat) : Wants :=
  let w := connectionWants cfg s now
  let deadline := s.reqs.fold (init := none) fun due t r =>
    if r.delivered then due else
    let ms := r.deadline - now
    match due with
    | some (_, earliest) => if ms < earliest then some (t, ms) else due
    | none => some (t, ms)
  let retry := s.reqs.fold (init := none) fun due t r =>
    match r.retryAt with
    | none => due
    | some time =>
      let ms := time - now
      match due with
      | some (_, earliest) => if ms < earliest then some (t, ms) else due
      | none => some (t, ms)
  { w with deadline, resume := owes cfg s, retry }

end Std.Http.Client.Driver
