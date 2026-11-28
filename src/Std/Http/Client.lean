/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Async.Timer
public import Std.Http.Transport.Outbox
public import Std.Http.Client.CookieHandler
public import Std.Http.Client.Proxy
public import Std.Http.Client.Authenticator
public import Std.Http.Client.Interceptor
public import Std.Http.Client.Config
public import Std.Http.Client.Error
public import Std.Http.Client.Connection.Driver
public import Std.Http.Client.Pool.Driver
public import Std.Http.Client.Connector
public import Std.Http.Client.Hop.Driver
public import Std.Http.Client.Driver

public section

/-!
# HTTP Client

An HTTP/1.1 client that opens connections, reuses them across requests, follows redirects, answers
authentication challenges, and retries connection-level failures.

Every decision is `Client.Driver`'s. `Client` is its interpreter: one actor task owns the driver's
state and reads a mailbox. Callers post their requests there, and the background tasks the actor
starts post what they saw: bytes from a socket, writes completing, a request body chunk, a caller
waiting for more of a response body, a timer firing. The actor reports each of these to the driver
and performs the commands the driver answers with. Writes go through an `Outbox` per connection, and
transports are opened by a `Connector`, so plain TCP, TLS and mock transports plug in the same way.

Use `Client.new` to create a client, then `client.send` (or `client.get` for a URL) to send requests.
-/

namespace Std.Http.Client

set_option linter.all true in
/--
The trailer fields of a response the client received, kept in its extensions: read them with
`Response.trailers`.
-/
structure Trailers where
  /-- Resolves once the response body ends: with its trailer fields, or `none` without any. -/
  task : Task (Option Headers)
deriving TypeName

end Std.Http.Client

set_option linter.all true in
/--
The trailer fields that ended the body of a response the client received, once the body ends:
`none` when it ended without any, failed, or the response came from elsewhere. Fields that may not
appear in a trailer (RFC 9110 §6.5.1) are dropped, and none of them is applied to the response.
-/
def Std.Http.Response.trailers (response : Response α) : Task (Option Headers) :=
  match response.extensions.get Client.Trailers with
  | some trailers => trailers.task
  | none => .pure none

namespace Std.Http.Client.Interpreter

open Std Async Protocol
open Internal (Outbox)

set_option linter.all true

/--
What the client's actor is told: the callers' requests, and what its background tasks saw.
-/
inductive Message where
  /-- A caller sends `request` to `origin`, and waits on `promise` for the response. -/
  | submit (ticket : Driver.Ticket) (origin : URI.Origin) (request : Request Body.Any)
      (size : Option Body.Length) (overrides : RequestOverrides)
      (promise : IO.Promise (Except Error (Response Body.Stream)))
  /-- An input for the driver, as it stands. -/
  | input (input : Driver.Input)
  /-- Connection `id` was opened over `transport`. -/
  | opened (id : Driver.ConnectionId) (transport : AnyTransport)
  /-- A receive on connection `id` ended. -/
  | received (id : Driver.ConnectionId) (result : Except IO.Error (Option ByteArray))
  /-- The writes of connection `id` all completed. -/
  | writesIdle (id : Driver.ConnectionId)
  /-- The writes of connection `id` ran late; then they completed, or the outbox `failed`. -/
  | writesLate (id : Driver.ConnectionId) (failed : Bool)
  /-- The body of request `ticket`, pulled for connection `id`, returned `input`. -/
  | pulled (ticket : Driver.Ticket) (id : Driver.ConnectionId) (input : Driver.RequestInput)
  /-- The caller of request `ticket` waits for more of the response body, or closed it. -/
  | interest (ticket : Driver.Ticket) (wanted : Bool)
  /-- The caller of request `ticket` closed the response body. -/
  | closed (ticket : Driver.Ticket)
  /-- The timer armed as `generation` fired. -/
  | timer (generation : Nat)
  /-- The client closes; `done` resolves once the driver took it. -/
  | close (done : IO.Promise Unit)

instance : Inhabited Message := ⟨.timer 0⟩

/-- A connection's resources, and the background tasks running for it. -/
private structure Conn where
  transport : AnyTransport
  outbox : Outbox AnyTransport
  reading : Bool := false
  watchingIdle : Bool := false
  watchingLate : Bool := false
  /-- The transport was closed already, by `Client.close`. -/
  closed : Bool := false

/-- A request's resources, and the background tasks running for it. -/
private structure Req where
  request : Request Body.Any
  promise : IO.Promise (Except Error (Response Body.Stream))
  /-- The body this hop sends, or `none` for no content. -/
  body : Option Body.Any := none
  /-- Rewinding the body failed: its next pull reports this. -/
  bodyError : Option IO.Error := none
  pulling : Bool := false
  response : Option Body.Stream := none
  /-- Resolved with the response's trailer fields, or `none` once its body ended without them. -/
  trailers : Option (IO.Promise (Option Headers)) := none
  /-- A chunk handed to the response body in the background, which its close waits for. -/
  delivery : Option (Task (Except IO.Error Unit)) := none
  watchingInterest : Bool := false
  watchingClosed : Bool := false

/-- What the actor keeps for the client's whole life. -/
private structure Env where
  config : Config
  connect : Connector
  mailbox : Std.Channel Message

/-- What the armed timer fires for. -/
private inductive Alarm where
  /-- A timer of a connection. -/
  | connection (id : Driver.ConnectionId) (timer : Connection.Driver.Timer)
  /-- The response deadline of a request. -/
  | expiry (ticket : Driver.Ticket)
  /-- The next attempt of a request. -/
  | retry (ticket : Driver.Ticket)
deriving BEq

/-- The writes one batch of commands handed to a connection. -/
private structure Batch where
  ok : Bool := true
  queued : Nat := 0
  /-- The batch waits for its writes: `some true` for a flush, `some false` for `awaitWritten`. -/
  await : Option Bool := none

/-- The actor's state. -/
private structure Actor where
  driver : Driver.State
  conns : Std.HashMap Driver.ConnectionId Conn := {}
  reqs : Std.HashMap Driver.Ticket Req := {}
  /--
  Inputs for a connection that arrived while it was not waiting on its sources, which would drop
  them; delivered in order once it waits again.
  -/
  deferred : Std.HashMap Driver.ConnectionId (Array Driver.Input) := {}
  /-- The timer armed: what it fires for, its deadline and the sleep behind it. -/
  timer : Option (Alarm × Nat × Sleep) := none
  generation : Nat := 0

/-- The most bytes queued behind the write in flight before the request body stops being pulled. -/
private def maxQueuedBytes : Nat := 65536

private def post (env : Env) (msg : Message) : BaseIO Unit :=
  discard <| env.mailbox.send msg

/-! ## Opening connections -/

/--
Opens a transport for `origin` under `Config.connectTimeout`, which bounds DNS resolution and the
connect. An exception thrown by the connector is reported as `Error.connect`.
-/
private def openTransport (env : Env) (origin : URI.Origin) : Async (Except Error AnyTransport) := do
  let resultChannel : Std.Channel (Except Error AnyTransport) ← Std.Channel.new
  let connectTask ← async (t := AsyncTask) do
    try env.connect origin env.config
    catch err => pure (.error (.connect (toString err)))
  BaseIO.chainTask connectTask fun
    | .ok result => discard <| resultChannel.send result
    | .error err => discard <| resultChannel.send (.error (.connect (toString err)))
  let outcome ← Selectable.one #[
    .case resultChannel.recvSelector (fun result => pure (some result)),
    .case (← Selector.sleep env.config.connectTimeout.val) (fun _ => pure none)]
  match outcome with
  | some result => return result
  | none =>
    -- The connector may still complete after the timeout: close the late transport.
    background do
      let late ← Selectable.one #[.case resultChannel.recvSelector pure]
      if let .ok transport := late then
        transport.close
    let timeout := env.config.connectTimeout.val
    return .error (.connect s!"connecting to {origin.host}:{origin.port} timed out after {timeout}ms")

private def dial (env : Env) (id : Driver.ConnectionId) (origin : URI.Origin) : Async Unit :=
  background do
    match ← (try openTransport env origin catch err => pure (.error (.io err))) with
    | .ok transport => post env (.opened id transport)
    | .error err => post env (.input (.dialed id (.error err)))

/-! ## Performing commands -/

private def closeRequestBody (r : Req) : Async Req := do
  if let some body := r.body then
    try body.close catch _ => pure ()
  return { r with body := none }

/--
Closes the response body once the chunk handed to it in the background is taken, so the caller
receives every chunk before the end.
-/
private def closeResponse (r : Req) : Async Req := do
  r.trailers.forM (·.resolve none)
  if let some stream := r.response then
    match r.delivery with
    | none => try stream.close catch _ => pure ()
    | some task =>
      background do
        try discard <| Async.ofTask task catch _ => pure ()
        try stream.close catch _ => pure ()
  return { r with response := none, delivery := none }

/-- Performs a command for the caller of request `t`; returns an input to report at once, if any. -/
private def performRequest (env : Env) (a : Actor) (t : Driver.Ticket) :
    Driver.RequestCommand → Async (Actor × Option Driver.Input)
  | .loadCookies origin target => do
    match env.config.cookieHandler with
    | none => post env (.input (.cookies t #[]))
    | some handler =>
      background do
        -- The request waits for its cookies, so a failing handler fails it before it is sent.
        let loaded : Except IO.Error (Array Header.Value) ←
          try .ok <$> handler.load origin target catch err => pure (.error err)
        match loaded with
        | .ok values => post env (.input (.cookies t values))
        | .error err => post env (.input (.cancel t (.io err)))
    return (a, none)
  | .storeCookies origin target headers => do
    -- Stored before the actor goes on, so a later request's `loadCookies` sees them.
    if let some handler := env.config.cookieHandler then
      try handler.store origin target headers catch _ => pure ()
    return (a, none)
  | .authenticate challenge => do
    match env.config.authenticator with
    | none => post env (.input (.credential t none))
    | some authenticator =>
      background do
        let value ← try authenticator.authenticate challenge catch _ => pure none
        post env (.input (.credential t value))
    return (a, none)
  | .intercept origin head => do
    match env.config.interceptor with
    | none => post env (.input (.intercepted t (.ok head)))
    | some interceptor =>
      background do
        let result ← try interceptor.onRequest origin head catch err => pure (.error (.io err))
        post env (.input (.intercepted t result))
    return (a, none)
  | .observe origin request head => do
    if let some interceptor := env.config.interceptor then
      background do try interceptor.onResponse origin request head catch _ => pure ()
    return (a, none)
  | .informational origin request head => do
    if let some interceptor := env.config.interceptor then
      background do try interceptor.onInformational origin request head catch _ => pure ()
    return (a, none)
  | cmd => do
    let some r := a.reqs[t]? | return (a, none)
    let r ← match cmd with
      | .body .original => pure { r with body := some r.request.body, bodyError := none }
      | .body .rewound => do
        -- Rewinding runs the body's own code: its failure fails the request, below.
        let bodyError ← match r.request.body.reset? with
          | some reset => try reset; pure none catch err => pure (some err)
          | none => pure none
        pure { r with body := some r.request.body, bodyError }
      | .body .empty => pure { r with body := none, bodyError := none }
      | .respond head size => do
        let stream ← Body.mkStream
        try stream.setKnownSize size catch _ => pure ()
        let trailers ← IO.Promise.new
        let extensions := Extensions.empty.insert (Trailers.mk (trailers.result?.map (·.join)))
        r.promise.resolve (.ok { line := head, body := stream, extensions })
        pure { r with response := some stream, trailers := some trailers }
      | .trailers fields => do
        r.trailers.forM (·.resolve (some fields))
        pure r
      | .offerBody chunk _ => do
        let some stream := r.response | pure r
        -- The driver offers a chunk once the caller waits for one, so it is usually taken at once.
        -- A caller whose wait lost a race gets it from a send that blocks in the background.
        if ← (try stream.trySend chunk catch _ => pure true) then
          pure { r with delivery := none }
        else
          pure { r with delivery := some (← (stream.send chunk).asTask) }
      | .endResponse => closeResponse r
      | .closeRequestBody => closeRequestBody r
      | .complete => do
        let r ← closeRequestBody r
        closeResponse r
      | .fail err => do
        let r ← closeRequestBody r
        r.promise.resolve (.error err)
        if let some stream := r.response then
          try stream.closeWithError err.toIOError catch _ => pure ()
        pure { r with response := none, delivery := none }
      | _ => pure r
    match cmd, r.bodyError with
    | .complete, _ | .fail _, _ => return ({ a with reqs := a.reqs.erase t }, none)
    | .body .rewound, some err => return ({ a with reqs := a.reqs.insert t r }, some (.cancel t (.io err)))
    | _, _ => return ({ a with reqs := a.reqs.insert t r }, none)

/-- Where the writes of `outbox` stand after a batch whose writes succeeded when `ok`. -/
private def writesOf (outbox : Outbox AnyTransport) (ok : Bool) (queued : Nat) :
    BaseIO Connection.Driver.Writes := do
  if !ok then return .idle
  if queued > maxQueuedBytes then return .backlogged
  if ← outbox.writing then return .inFlight
  return .idle

/-- Waits for the writes of a batch that asked to, then reports them. -/
private def reportWritten (env : Env) (id : Driver.ConnectionId) (outbox : Outbox AnyTransport)
    (flush : Bool) : Async Unit := do
  let ok ← try
      if flush then
        outbox.awaitIdle
        pure !(← outbox.failed)
      else outbox.awaitWritten
    catch _ => pure false
  post env (.input (.connection id (.written ok (← writesOf outbox ok 0))))

/--
Performs the driver's commands in order. Each connection the commands wrote to is reported
`written` once for the batch: at once, or after its writes complete when the batch waits for them.
Returns the inputs reported at once.
-/
private def perform (env : Env) (a : Actor) (cmds : Array Driver.Command) :
    Async (Actor × Array Driver.Input) := do
  let mut a := a
  let mut now : Array Driver.Input := #[]
  let mut batches : Array (Driver.ConnectionId × Batch) := #[]
  for cmd in cmds do
    match cmd with
    | .dial id origin => dial env id origin
    | .request t rc =>
      let (a', input) ← performRequest env a t rc
      a := a'
      if let some input := input then now := now.push input
    | .connection id cc =>
      let some c := a.conns[id]? | continue
      if let .close := cc then
        batches := batches.filter (·.1 != id)
        a := { a with conns := a.conns.erase id, deferred := a.deferred.erase id }
        unless c.closed do
          try c.transport.close catch _ => pure ()
        c.outbox.stop
        continue
      let b := ((batches.find? (·.1 == id)).map (·.2)).getD {}
      let b ← match cc with
        | .write data =>
          if !b.ok then pure b
          else match ← c.outbox.send data with
            | some queued => pure { b with queued }
            | none => pure { b with ok := false }
        | .awaitWritten => pure { b with await := some false }
        | .flush => pure { b with await := some true }
        | .close => pure b
      batches := (batches.filter (·.1 != id)).push (id, b)
  for (id, b) in batches do
    let some c := a.conns[id]? | continue
    match b.await, b.ok with
    | some flush, true => background (reportWritten env id c.outbox flush)
    | _, ok =>
      -- A write can fail after `send` returned, before the batch is reported.
      let ok := ok && !(← c.outbox.failed)
      now := now.push (.connection id (.written ok (← writesOf c.outbox ok b.queued)))
  return (a, now)

/-! ## Stepping the driver -/

/-- Reports `inputs` to the driver in order, with every input the commands it answers report at once. -/
private def stepAll (env : Env) (a : Actor) (inputs : Array Driver.Input) : Async Actor := do
  let mut a := a
  let mut pending := inputs.toList
  repeat
    match pending with
    | [] => break
    | input :: rest =>
      let (driver, cmds) := Driver.step env.config a.driver (← IO.monoMsNow) input
      let (a', more) ← perform env { a with driver } cmds
      a := a'
      pending := rest ++ more.toList
  return a

/-- Whether connection `id` waits on its sources, so an input for it is not dropped. -/
private def waiting (a : Actor) (id : Driver.ConnectionId) : Bool :=
  a.driver.conns[id]?.any (·.driver.waits)

/-- Reports `input` for connection `id`, or keeps it until the connection waits on its sources. -/
private def deliver (env : Env) (a : Actor) (id : Driver.ConnectionId) (input : Driver.Input) :
    Async Actor := do
  if !a.driver.conns.contains id then return a
  if waiting a id then stepAll env a #[input]
  else return { a with deferred := a.deferred.insert id ((a.deferred.getD id #[]).push input) }

/-- Delivers the inputs kept for connections that wait on their sources again. -/
private def flushDeferred (env : Env) (a : Actor) : Async Actor := do
  let mut a := a
  repeat
    let next := a.deferred.fold (init := none) fun found id inputs =>
      match found with
      | some _ => found
      | none =>
        if !a.driver.conns.contains id then some (id, none)
        else if waiting a id then (inputs[0]?.map fun i => (id, some (i, inputs.extract 1))) else none
    match next with
    | none => break
    | some (id, none) => a := { a with deferred := a.deferred.erase id }
    | some (id, some (input, rest)) =>
      a := { a with deferred := if rest.isEmpty then a.deferred.erase id else a.deferred.insert id rest }
      a ← stepAll env a #[input]
  return a

/-! ## Waiting -/

/-- A selector's first value, in the background, posted as a message. -/
private def watch (env : Env) (selector : Selector α) (msg : α → Message) : Async Unit :=
  background do
    try post env (msg (← Selectable.one #[.case selector pure])) catch _ => pure ()

/--
Starts the background tasks for what the driver waits on that none runs for yet, and arms the timer
due first.
-/
private def arm (env : Env) (a : Actor) : Async Actor := do
  let now ← IO.monoMsNow
  let w := Driver.wants env.config a.driver now
  let mut a := a
  for (id, size) in w.recv do
    let some c := a.conns[id]? | continue
    unless c.reading do
      a := { a with conns := a.conns.insert id { c with reading := true } }
      background do
        let result ← try .ok <$> c.transport.recv size.toUInt64 catch err => pure (.error err)
        post env (.received id result)
  for id in w.writesIdle do
    let some c := a.conns[id]? | continue
    unless c.watchingIdle do
      a := { a with conns := a.conns.insert id { c with watchingIdle := true } }
      match ← c.outbox.idle? with
      | none => post env (.writesIdle id)
      | some idle =>
        background do
          discard <| Async.ofTask idle
          post env (.writesIdle id)
  for id in w.writesLate do
    let some c := a.conns[id]? | continue
    unless c.watchingLate do
      a := { a with conns := a.conns.insert id { c with watchingLate := true } }
      let late ← c.outbox.lateSelector
      background do
        discard <| Selectable.one #[.case late pure]
        -- A write that completed meanwhile renewed the timer; otherwise this fails the writes.
        try c.outbox.awaitIdle catch _ => pure ()
        post env (.writesLate id (← c.outbox.failed))
  for t in w.requestBody do
    let some r := a.reqs[t]? | continue
    let some id := a.driver.reqs[t]? |>.bind (·.connection) | continue
    unless r.pulling do
      a := { a with reqs := a.reqs.insert t { r with pulling := true } }
      match r.bodyError, r.body with
      | some err, _ => post env (.pulled t id (.pullFailed err))
      | none, none => post env (.pulled t id (.pulled none))
      | none, some body =>
        background do
          let input ← try .pulled <$> body.recv catch err => pure (.pullFailed err)
          post env (.pulled t id input)
  for t in w.responseInterest do
    let some r := a.reqs[t]? | continue
    let some stream := r.response | continue
    unless r.watchingInterest do
      a := { a with reqs := a.reqs.insert t { r with watchingInterest := true } }
      watch env stream.interestSelector (.interest t)
  for t in w.responseClosed do
    let some r := a.reqs[t]? | continue
    let some stream := r.response | continue
    -- The caller waiting for more also reports a close.
    unless r.watchingInterest || r.watchingClosed do
      a := { a with reqs := a.reqs.insert t { r with watchingClosed := true } }
      watch env stream.closedSelector fun _ => .closed t
  if w.resume then post env (.input .resume)
  let due : Option (Alarm × Nat) :=
    match w.timer.map (fun (id, timer, ms) => (Alarm.connection id timer, ms)),
        w.deadline.map (fun (t, ms) => (Alarm.expiry t, ms)) with
    | some (c, ms), some (e, ms') => if ms' < ms then some (e, ms') else some (c, ms)
    | some due, none | none, some due => some due
    | none, none => none
  let due : Option (Alarm × Nat) :=
    match due, w.retry.map (fun (t, ms) => (Alarm.retry t, ms)) with
    | some (c, ms), some (r, ms') => if ms' < ms then some (r, ms') else some (c, ms)
    | some due, none | none, some due => some due
    | none, none => none
  match due, a.timer with
  | none, none => return a
  | none, some (_, _, sleep) =>
    sleep.stop
    return { a with timer := none }
  | some (alarm, ms), armed =>
    let deadline := now + ms
    if let some (alarm', deadline', _) := armed then
      if alarm' == alarm && deadline' == deadline then return a
    if let some (_, _, sleep) := armed then sleep.stop
    let generation := a.generation + 1
    let sleep ← Sleep.mk (.ofNat ms)
    background do
      try sleep.wait; post env (.timer generation) catch _ => pure ()
    return { a with timer := some (alarm, deadline, sleep), generation }

/--
Reports that the writes of connection `c` stopped: idle, or failed after the batch that started
them was reported. The writes a watcher saw complete may be followed by more handed over since.
-/
private def writesSettled (env : Env) (a : Actor) (id : Driver.ConnectionId) (c : Conn) :
    Async Actor := do
  -- While the connection writes, the report of its batch carries the failure instead.
  if ← c.outbox.failed then
    if waiting a id then stepAll env a #[.connection id (.written false .idle)] else return a
  else if ← c.outbox.writing then return a
  else deliver env a id (.connection id .writesIdle)

/-! ## The actor -/

/-- Handles one message. -/
private def handle (env : Env) (a : Actor) : Message → Async Actor
  | .submit t origin request size overrides promise => do
    let a := { a with reqs := a.reqs.insert t { request, promise } }
    let replayable := request.body.reset?.isSome
    stepAll env a #[.submit t origin request.line size overrides replayable]
  -- What a connection's writes report is the input it waits for while it writes.
  | .input input@(.connection _ (.written ..)) => stepAll env a #[input]
  | .input input@(.connection id _) => deliver env a id input
  | .input input => stepAll env a #[input]
  | .opened id transport => do
    let outbox ← Outbox.new transport env.config.requestTimeout.val.toInt.toNat
      (maxWriteBytes := some maxQueuedBytes)
    let a := { a with conns := a.conns.insert id { transport, outbox } }
    let a ← stepAll env a #[.dialed id (.ok ())]
    -- A connection the pool no longer wants, as after the client closed meanwhile.
    if a.driver.conns.contains id then return a
    try transport.close catch _ => pure ()
    outbox.stop
    return { a with conns := a.conns.erase id }
  | .received id result => do
    let some c := a.conns[id]? | return a
    let a := { a with conns := a.conns.insert id { c with reading := false } }
    deliver env a id (.connection id (match result with
      | .ok data => .received data
      | .error err => .failed err))
  | .writesIdle id => do
    let some c := a.conns[id]? | return a
    let a := { a with conns := a.conns.insert id { c with watchingIdle := false } }
    writesSettled env a id c
  | .writesLate id failed => do
    let some c := a.conns[id]? | return a
    let a := { a with conns := a.conns.insert id { c with watchingLate := false } }
    if failed then deliver env a id (.connection id (.fired .request))
    else writesSettled env a id c
  | .pulled t id input => do
    let some r := a.reqs[t]? | return a
    let a := { a with reqs := a.reqs.insert t { r with pulling := false } }
    -- A chunk pulled for a hop that has since moved on is not this hop's.
    if (a.driver.reqs[t]?.bind (·.connection)) != some id then return a
    deliver env a id (.request t input)
  | .interest t wanted => do
    let some r := a.reqs[t]? | return a
    let a := { a with reqs := a.reqs.insert t { r with watchingInterest := false } }
    let some id := a.driver.reqs[t]? |>.bind (·.connection) | return a
    deliver env a id (.request t (.bodyInterest wanted))
  | .closed t => do
    let some r := a.reqs[t]? | return a
    let a := { a with reqs := a.reqs.insert t { r with watchingClosed := false } }
    let some id := a.driver.reqs[t]? |>.bind (·.connection) | return a
    deliver env a id (.request t (.bodyInterest false))
  | .timer generation => do
    let some (alarm, _, _) := a.timer | return a
    if generation != a.generation then return a
    let a := { a with timer := none }
    match alarm with
    -- A timer is armed afresh after every step: one that fires while its connection is not
    -- waiting belongs to a wait that is over.
    | .connection id timer =>
      if waiting a id then stepAll env a #[.connection id (.fired timer)] else return a
    | .expiry t => stepAll env a #[.expired t]
    | .retry t => stepAll env a #[.retryDue t]
  | .close done => do
    -- The driver closes each connection after a flush, which a peer that stopped reading would
    -- hold up: `close` closes the transports at once, failing the writes in flight.
    let mut a := a
    for (id, c) in a.conns.toList do
      unless c.closed do
        try c.transport.close catch _ => pure ()
        a := { a with conns := a.conns.insert id { c with closed := true } }
    a ← stepAll env a #[.close]
    done.resolve ()
    return a

/-- Runs the actor: handles each message, then waits on what the driver waits on. -/
private def run (env : Env) (a : Actor) : Async Unit := do
  let mut a := a
  repeat
    let msg ← await (← env.mailbox.recv)
    a ← handle env a msg
    a ← flushDeferred env a
    a ← arm env a

end Std.Http.Client.Interpreter

namespace Std.Http

open Std Async

/--
An HTTP client: a pool of reusable connections per origin, the configuration they are opened with,
and the redirect, retry and authentication policy applied to every request.
-/
structure Client where
  /-- The configuration of the client and of the connections it opens. -/
  config : Client.Config
  /-- The mailbox of the client's actor. -/
  mailbox : Std.Channel Client.Interpreter.Message
  /-- The ticket of the next request. -/
  nextTicket : IO.Ref Nat

namespace Client

open Interpreter

/-- A selector that fires once `promise` is resolved. -/
private def promiseSelector (promise : IO.Promise α) : Selector Unit where
  tryFn := do
    if ← promise.isResolved then return some () else return none
  registerFn waiter :=
    BaseIO.chainTask (sync := true) promise.result? fun _ =>
      waiter.race (pure ()) (fun p => p.resolve (.ok ()))
  unregisterFn := pure ()

/--
Creates a client with no open connection and starts its actor. Supply a custom `connect` function
(e.g. a TLS connector or a mock) to customize how transports are opened.

`maxRetries` bounds how many times a failed request is sent again on a fresh connection. Retries
only follow connection-level failures (see `Error.isRetryable`); responses, `4xx` and `5xx` included,
are never retried. A request with an idempotent method and a replayable body is retried after any
such failure; any other request, a `POST` for instance, only after a failure that proves it never
reached a server (`Error.isNeverSent`), so it is never sent twice.
-/
def new (config : Config := {}) (connect : Connector := Connector.tcp) (maxRetries : Nat := 1) :
    Async Client := do
  let mailbox ← Std.Channel.new
  let env : Env := { config, connect, mailbox }
  background (run env { driver := { maxRetries } })
  return { config, mailbox, nextTicket := ← IO.mkRef 0 }

/--
Sends a request to `origin`, following redirects and answering authentication challenges, and
returns the response or the typed `Error` that ended the request.

On a retryable connection-level failure the request is sent again, up to the client's `maxRetries`
times, on fresh connections, unless `close` ran since it started.

Every hop checks out a connection to its origin from the client's pool, which goes back to the pool
once its exchange completes. The caller must read the response body to its end or close it: until
then its connection carries no other request.

Cancelling `cancel` before the response head arrives fails the request with `Error.cancelled`, which
is never retried, and closes the connection carrying it. Once the head arrived, close the response
body instead.
-/
def trySend {β : Type} [Coe β Body.Any] (client : Client) (origin : URI.Origin)
    (request : Request β) (overrides : RequestOverrides := {})
    (cancel : Option CancellationContext := none) :
    Async (Except Error (Response Body.Stream)) := do
  let request : Request Body.Any := { request with }
  let size : Except IO.Error (Option Body.Length) ←
    try .ok <$> request.body.getKnownSize catch err => pure (.error err)
  let size ← match size with
    | .ok size => pure size
    | .error err => return .error (.io err)
  let ticket ← client.nextTicket.modifyGet fun t => (t, t + 1)
  let promise ← IO.Promise.new
  discard <| client.mailbox.send (.submit ticket origin request size overrides promise)
  if let some ctx := cancel then
    let answered ← Selectable.one #[
      .case (promiseSelector promise) fun _ => pure true,
      .case ctx.doneSelector fun _ => pure false]
    unless answered do
      discard <| client.mailbox.send (.input (.cancel ticket .cancelled))
  await promise.result!

/--
Sends a request to `origin`, following redirects and answering authentication challenges.
Use `trySend` to receive failures as a typed `Error` instead of a thrown exception.
-/
def send {β : Type} [Coe β Body.Any] (client : Client) (origin : URI.Origin) (request : Request β)
    (overrides : RequestOverrides := {}) (cancel : Option CancellationContext := none) :
    Async (Response Body.Stream) :=
  client.trySend origin request overrides cancel >>= Error.throwOrPure

/--
Sends a request whose target is an absolute URL (`http://host:8080/path?query`) to the origin that URL
names, like `trySend` with that origin. The target goes on the wire in origin-form (or in the
absolute-form a proxy needs), so any user information and fragment in the URL are not sent. Fails with
`Error.invalidRequest` when the target is not an absolute URL with a host.
-/
def tryExecute {β : Type} [Coe β Body.Any] (client : Client) (request : Request β)
    (overrides : RequestOverrides := {}) (cancel : Option CancellationContext := none) :
    Async (Except Error (Response Body.Stream)) := do
  let request : Request Body.Any := { request with }
  let .absoluteForm uri := request.line.uri
    | return .error (.invalidRequest
        s!"request target {request.line.uri} is not an absolute URL; use `trySend` with an origin")
  let some origin := uri.origin?
    | return .error (.invalidRequest s!"request target {request.line.uri} names no host")
  let request := { request with line := { request.line with uri := uri.originTarget } }
  client.trySend origin request overrides cancel

/--
Sends a request whose target is an absolute URL to the origin that URL names.
Use `tryExecute` to receive failures as a typed `Error` instead of a thrown exception.
-/
def execute {β : Type} [Coe β Body.Any] (client : Client) (request : Request β)
    (overrides : RequestOverrides := {}) (cancel : Option CancellationContext := none) :
    Async (Response Body.Stream) :=
  client.tryExecute request overrides cancel >>= Error.throwOrPure

/--
Sends a `GET` for `url` (`http://host:8080/path?query`). Fails with `Error.invalidRequest` when `url`
is not an absolute URL with a host.
-/
def tryGet (client : Client) (url : String) (overrides : RequestOverrides := {})
    (cancel : Option CancellationContext := none) : Async (Except Error (Response Body.Stream)) := do
  let some uri := URI.parse? url
    | return .error (.invalidRequest s!"not an absolute URL: {url.quote}")
  client.tryExecute (← Request.get (.absoluteForm uri) |>.empty) overrides cancel

/--
Sends a `GET` for `url` (`http://host:8080/path?query`).
Use `tryGet` to receive failures as a typed `Error` instead of a thrown exception.
-/
def get (client : Client) (url : String) (overrides : RequestOverrides := {})
    (cancel : Option CancellationContext := none) : Async (Response Body.Stream) :=
  client.tryGet url overrides cancel >>= Error.throwOrPure

/--
Closes every connection the client holds, aborting the exchanges in flight on them, and fails every
request already started, none of which is retried. The client remains usable: a later `send` opens
fresh connections.
-/
def close (client : Client) : Async Unit := do
  let done ← IO.Promise.new
  discard <| client.mailbox.send (.close done)
  await done.result!

end Client
end Std.Http
