/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init.Data.Queue
public import Std.Http.Client.Config
public import Std.Http.Client.Error

public section

/-!
# Pool driver

The decisions of a client's connection pool, without I/O. For each origin the pool keeps the
connections it opened, which of them are idle, the ones being opened, and the requests waiting for
one. It decides whether a request reuses an idle connection, opens a new one while the origin is
under `Config.maxConnectionsPerOrigin`, or waits; who gets a connection that comes free or a place
under the limit that a closed connection leaves; and what `close` ends.

The pool is the driver's interpreter. It names each request asking for a connection with a
`Ticket`, reports what happened as the next `Input`, and performs the `Command`s that `step`
returns: opening a connection (`dial`, which names it), handing one to a request (`grant`), failing
a request (`reject`), and closing a connection (`closeConnection`). Every ticket is answered once,
by `grant` or `reject`.

A connection holds its place under the limit from the `dial` that names it until the interpreter
reports its loop has exited (`connectionClosed`), so the limit also bounds connections being opened
and connections being torn down. A connection that ends on its own, as when its keep-alive timeout
passes or the peer closes it, still finishes its writes before its loop exits; the interpreter
reports `retired` as soon as the connection's driver stops accepting requests, so the pool does not
grant it in the meantime.
-/

namespace Std.Http.Client.Pool.Driver

set_option linter.all true

open Std Http

/--
Names a request waiting for a connection. The interpreter chooses it, unique among the requests
that have not been answered.
-/
abbrev Ticket := Nat

/--
Names a connection. The driver chooses it when it asks for the connection to be opened.
-/
abbrev ConnectionId := Nat

/--
What the interpreter reports to the driver.
-/
inductive Input where
  /--
  A request needs a connection to `origin`. A `fresh` one, used to retry a failed request, never
  reuses an idle connection, which may have gone stale the same way.
  -/
  | acquire (ticket : Ticket) (origin : URI.Origin) (fresh : Bool)

  /--
  Opening connection `id` ended, with the error that failed it.
  -/
  | dialed (id : ConnectionId) (result : Except Client.Error Unit)

  /--
  The request that held connection `id` is done with it. A `reusable` connection can carry another
  request; any other is closed.
  -/
  | released (id : ConnectionId) (reusable : Bool)

  /--
  Connection `id` takes no further request: it ends on its own, and its loop's exit follows as
  `connectionClosed id`. Reported when the connection's driver issues `stopAccepting`, idle or held.
  -/
  | retired (id : ConnectionId)

  /--
  The loop of connection `id` exited, however it ended.
  -/
  | connectionClosed (id : ConnectionId)

  /--
  The client closes: every connection closes and every request not yet answered fails. The pool
  stays usable, and a later `acquire` opens fresh connections.
  -/
  | close

/--
What the driver asks the interpreter to do.
-/
inductive Command where
  /--
  Open connection `id` to `origin` for `ticket`, then report `dialed id`.
  -/
  | dial (ticket : Ticket) (origin : URI.Origin) (id : ConnectionId)

  /--
  Hand connection `id` to `ticket`, which holds it until it reports `released id`.
  -/
  | grant (ticket : Ticket) (id : ConnectionId)

  /--
  Fail `ticket` with `err`.
  -/
  | reject (ticket : Ticket) (err : Client.Error)

  /--
  Close connection `id`, aborting any exchange on it. Its loop's exit is reported as
  `connectionClosed id`.
  -/
  | closeConnection (id : ConnectionId)

/--
A connection being opened.
-/
structure Dial where
  /--
  The connection's name.
  -/
  id : ConnectionId

  /--
  The request it is opened for.
  -/
  ticket : Ticket

  /--
  `close` ran since the dial started, and its request was already rejected.
  -/
  cancelled : Bool := false

/--
The connections of one origin, and the requests waiting for one of them.
-/
structure OriginPool where
  /--
  The origin every connection here was opened for.
  -/
  origin : URI.Origin

  /--
  Every connection opened here whose loop has not exited: idle, held by a request, or closing.
  -/
  connections : Array ConnectionId := #[]

  /--
  The connections no request holds, most recently released last.
  -/
  idle : Array ConnectionId := #[]

  /--
  The connections told to close, which no request gets again.
  -/
  closing : Array ConnectionId := #[]

  /--
  The connections being opened.
  -/
  dials : Array Dial := #[]

  /--
  The requests waiting for a connection, oldest first.
  -/
  waiters : Std.Queue Ticket := .empty

namespace OriginPool

/--
The number of places under `Config.maxConnectionsPerOrigin` the pool holds: connections open or
closing, and connections being opened.
-/
def size (pool : OriginPool) : Nat :=
  pool.connections.size + pool.dials.size

/--
`true` when the pool holds no connection and no request waits, so the driver can drop it.
-/
def isUnused (pool : OriginPool) : Bool :=
  pool.size == 0 && pool.waiters.isEmpty

/--
Opens connection `id` for `ticket`, in a place under the limit.
-/
private def dial (pool : OriginPool) (ticket : Ticket) (id : ConnectionId) :
    OriginPool × Array Command :=
  ({ pool with dials := pool.dials.push { id, ticket } }, #[.dial ticket pool.origin id])

/--
Passes a place under the limit that the pool has just freed to its oldest waiting request, which
opens connection `id` in it.
-/
private def passPlace (pool : OriginPool) (id : ConnectionId) : OriginPool × Array Command :=
  match pool.waiters.dequeue? with
  | some (ticket, waiters) => { pool with waiters }.dial ticket id
  | none => (pool, #[])

/--
Takes the most recently released idle connection, opens connection `id` while under `limit`, or
queues the request. A `fresh` request skips the idle connections, and at the limit closes the least
recently used one to make room: the request waits for a place like any other, since the closing
connection keeps its own until its loop exits.
-/
private def acquire (limit : Nat) (pool : OriginPool) (ticket : Ticket) (fresh : Bool)
    (id : ConnectionId) : OriginPool × Array Command :=
  match fresh, pool.idle.back? with
  | false, some conn => ({ pool with idle := pool.idle.pop }, #[.grant ticket conn])
  | _, _ =>
    if pool.size < limit then
      pool.dial ticket id
    else
      let pool := { pool with waiters := pool.waiters.enqueue ticket }
      match fresh, pool.idle[0]? with
      | true, some oldest =>
        ({ pool with idle := pool.idle.extract 1, closing := pool.closing.push oldest },
          #[.closeConnection oldest])
      | _, _ => (pool, #[])

/--
Grants connection `id`, just opened, to its request. A dial `close` cancelled closes the connection
instead, and a failed one fails its request and passes its place on, to open connection `next`.
-/
private def dialed (pool : OriginPool) (id : ConnectionId) (result : Except Client.Error Unit)
    (next : ConnectionId) : OriginPool × Array Command :=
  match pool.dials.find? (·.id == id) with
  | none => (pool, #[])
  | some dial =>
    let pool := { pool with dials := pool.dials.filter (·.id != id) }
    match result, dial.cancelled with
    | .ok (), false =>
      ({ pool with connections := pool.connections.push id }, #[.grant dial.ticket id])
    | .ok (), true =>
      ({ pool with connections := pool.connections.push id, closing := pool.closing.push id },
        #[.closeConnection id])
    | .error err, cancelled =>
      let (pool, more) := pool.passPlace next
      (pool, (if cancelled then #[] else #[.reject dial.ticket err]) ++ more)

/--
Takes back connection `id` from the request that held it: to the oldest waiting request, else to
the idle connections, when `reusable`; closed otherwise. A connection already closing, or not held,
is left as it is.
-/
private def released (pool : OriginPool) (id : ConnectionId) (reusable : Bool) :
    OriginPool × Array Command :=
  if !pool.connections.contains id || pool.closing.contains id || pool.idle.contains id then
    (pool, #[])
  else if reusable then
    match pool.waiters.dequeue? with
    | some (ticket, waiters) => ({ pool with waiters }, #[.grant ticket id])
    | none => ({ pool with idle := pool.idle.push id }, #[])
  else
    ({ pool with closing := pool.closing.push id }, #[.closeConnection id])

/--
Stops granting connection `id`, which is ending on its own. It keeps its place until its loop exits,
and a request that still holds it releases it to nothing.
-/
private def retired (pool : OriginPool) (id : ConnectionId) : OriginPool :=
  if !pool.connections.contains id || pool.closing.contains id then pool
  else { pool with idle := pool.idle.filter (· != id), closing := pool.closing.push id }

/--
Forgets connection `id`, whose loop exited, and passes its place on, to open connection `next`.
-/
private def connectionClosed (pool : OriginPool) (id : ConnectionId) (next : ConnectionId) :
    OriginPool × Array Command :=
  if !pool.connections.contains id then
    (pool, #[])
  else
    passPlace { pool with
      connections := pool.connections.filter (· != id)
      idle := pool.idle.filter (· != id)
      closing := pool.closing.filter (· != id) } next

/--
Fails the waiting requests and the ones whose connection is being opened, and closes every
connection not already closing.
-/
private def close (pool : OriginPool) : OriginPool × Array Command :=
  let waiting := pool.waiters.toArray.map fun ticket =>
    Command.reject ticket (.closed "client closed while the request waited for a connection")
  let dialing := pool.dials.filterMap fun dial =>
    if dial.cancelled then none
    else some (Command.reject dial.ticket
      (.closed "client closed while the connection was being opened"))
  let running := pool.connections.filter (!pool.closing.contains ·)
  ({ pool with
      waiters := .empty
      idle := #[]
      dials := pool.dials.map ({ · with cancelled := true })
      closing := pool.closing ++ running },
    waiting ++ dialing ++ running.map .closeConnection)

end OriginPool

/--
The state of the pool driver.
-/
structure State where
  /--
  A pool for each origin with a connection or a waiting request.
  -/
  pools : Array OriginPool := #[]

  /--
  The name of the next connection to open.
  -/
  nextId : ConnectionId := 0

namespace State

/--
The pool of `origin`, if it holds a connection or a waiting request.
-/
def pool? (s : State) (origin : URI.Origin) : Option OriginPool :=
  s.pools.find? (·.origin == origin)

/--
Applies `f` to the pool at `index` in `s.pools`, or to a new pool for `origin` when there is none,
gives `f` the next connection name, and drops the pool once `f` leaves it unused.
-/
private def update (s : State) (origin : URI.Origin) (index? : Option Nat)
    (f : OriginPool → ConnectionId → OriginPool × Array Command) : State × Array Command :=
  let pool := (index?.bind (s.pools[·]?)).getD { origin }
  let (pool, cmds) := f pool s.nextId
  let pools := match index?, pool.isUnused with
    | some index, true => s.pools.eraseIdx! index
    | some index, false => s.pools.set! index pool
    | none, true => s.pools
    | none, false => s.pools.push pool
  let opened := cmds.any fun | .dial .. => true | _ => false
  ({ pools, nextId := if opened then s.nextId + 1 else s.nextId }, cmds)

/--
Applies `f` to the pool of `origin`.
-/
private def withOrigin (s : State) (origin : URI.Origin)
    (f : OriginPool → ConnectionId → OriginPool × Array Command) : State × Array Command :=
  s.update origin (s.pools.findIdx? (·.origin == origin)) f

/--
Applies `f` to the pool that connection `id` belongs to, open or being opened. An unknown
connection changes nothing.
-/
private def withConnection (s : State) (id : ConnectionId)
    (f : OriginPool → ConnectionId → OriginPool × Array Command) : State × Array Command :=
  let owns (pool : OriginPool) := pool.connections.contains id || pool.dials.any (·.id == id)
  match s.pools.findIdx? owns with
  | some index =>
    match s.pools[index]? with
    | some pool => s.update pool.origin (some index) f
    | none => (s, #[])
  | none => (s, #[])

end State

/--
Applies one input.
-/
def step (cfg : Client.Config) (s : State) : Input → State × Array Command
  | .acquire ticket origin fresh =>
    s.withOrigin origin (·.acquire cfg.maxConnectionsPerOrigin.val ticket fresh ·)
  | .dialed id result => s.withConnection id (·.dialed id result ·)
  | .released id reusable => s.withConnection id fun pool _ => pool.released id reusable
  | .retired id => s.withConnection id fun pool _ => (pool.retired id, #[])
  | .connectionClosed id => s.withConnection id (·.connectionClosed id ·)
  | .close =>
    let (pools, cmds) := s.pools.foldl (init := (#[], #[])) fun (pools, cmds) pool =>
      let (pool, more) := pool.close
      (if pool.isUnused then pools else pools.push pool, cmds ++ more)
    ({ s with pools }, cmds)

end Std.Http.Client.Pool.Driver
