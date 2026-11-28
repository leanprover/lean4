import Std.Http

/-!
Tests the HTTP client pool driver (`Std.Http.Client.Pool.Driver`) without I/O: reusing idle
connections, connections that retire on their own, `maxConnectionsPerOrigin` and the requests that
wait at it, places passed on as connections close or fail to open, retries that skip idle connections,
separate origins (scheme, host and port, RFC 6454), `close`, inputs reported twice, and that every
request is answered once.
-/

open Std.Http Std.Http.Client Std.Http.Client.Pool.Driver

def cfg : Client.Config := { maxConnectionsPerOrigin := ⟨2, by decide⟩ }

def origin (host : String) : URI.Origin :=
  (URI.parse! s!"http://{host}/").origin?.getD
    { scheme := URI.Scheme.ofString! "http", host := .empty, port := 0 }

def a := origin "a"
def b := origin "b"

def tags (cmds : Array Command) : List String :=
  cmds.toList.map fun
    | .dial ticket o id => s!"dial {ticket} {o.host} #{id}"
    | .grant ticket id => s!"grant {ticket} #{id}"
    | .reject ticket err => s!"reject {ticket}: {err}"
    | .closeConnection id => s!"close #{id}"

/-- Applies `inputs` in order, collecting every command. -/
def run (inputs : List Input) (s : State := {}) (config : Client.Config := cfg) :
    State × Array Command :=
  inputs.foldl (init := (s, #[])) fun (s, cmds) input =>
    let (s, more) := step config s input
    (s, cmds ++ more)

def runTags (inputs : List Input) (s : State := {}) : List String := tags (run inputs s).2

def ok : Except Client.Error Unit := .ok ()
def refused : Except Client.Error Unit := .error (.connect "refused")

/-- The tickets `cmds` answer, in order. -/
def answered (cmds : Array Command) : List Nat :=
  cmds.toList.filterMap fun
    | .grant ticket _ | .reject ticket _ => some ticket
    | _ => none

/-! ## Opening and reusing -/

#guard runTags [.acquire 1 a false, .dialed 0 ok] == ["dial 1 a #0", "grant 1 #0"]

-- A released connection is reused, most recently released first.
#guard runTags [.acquire 1 a false, .dialed 0 ok, .acquire 2 a false, .dialed 1 ok,
    .released 0 true, .released 1 true, .acquire 3 a false] ==
  ["dial 1 a #0", "grant 1 #0", "dial 2 a #1", "grant 2 #1", "grant 3 #1"]

-- One that cannot carry another request is closed, and keeps its place until its loop exits.
#guard
  let (s, cmds) := run [.acquire 1 a false, .dialed 0 ok, .released 0 false]
  tags cmds == ["dial 1 a #0", "grant 1 #0", "close #0"] && (s.pool? a).any (·.size == 1) &&
    (run [.connectionClosed 0] s).1.pools.isEmpty

-- An idle connection that closes is forgotten.
#guard
  let (s, _) := run [.acquire 1 a false, .dialed 0 ok, .released 0 true, .connectionClosed 0]
  s.pools.isEmpty && runTags [.acquire 2 a false] s == ["dial 2 a #1"]

/-! ## Connections that end on their own -/

-- An idle connection that retires is never granted again, and keeps its place until its loop exits.
#guard
  let (s, _) := run [.acquire 1 a false, .acquire 2 a false, .dialed 0 ok, .dialed 1 ok,
    .released 0 true, .released 1 true, .retired 1]
  runTags [.acquire 3 a false] s == ["grant 3 #0"] &&
    runTags [.acquire 3 a false, .acquire 4 a false] s == ["grant 3 #0"] &&
    runTags [.acquire 3 a false, .acquire 4 a false, .connectionClosed 1] s == ["grant 3 #0", "dial 4 a #2"]

-- Retiring asks for no close: the connection is already ending.
#guard runTags [.acquire 1 a false, .dialed 0 ok, .released 0 true, .retired 0] ==
  ["dial 1 a #0", "grant 1 #0"]

-- A held connection that retires goes back to no one, even when released as reusable.
#guard
  let (s, _) := run [.acquire 1 a false, .acquire 2 a false, .acquire 3 a false, .dialed 0 ok,
    .dialed 1 ok, .retired 0]
  runTags [.released 0 true] s == [] && runTags [.released 0 true, .connectionClosed 0] s == ["dial 3 a #2"]

-- The last connection of an origin that retires and exits leaves no pool behind.
#guard (run [.acquire 1 a false, .dialed 0 ok, .released 0 true, .retired 0,
    .connectionClosed 0]).1.pools.isEmpty

-- Retiring a connection already closing, or twice, changes nothing.
#guard
  let (s, _) := run [.acquire 1 a false, .dialed 0 ok, .released 0 false]
  let closing (s : State) := (s.pool? a).map (·.closing.toList)
  closing (run [.retired 0, .retired 0] s).1 == closing s

/-! ## The limit -/

-- At the limit a request waits, and gets the next connection released.
#guard runTags [.acquire 1 a false, .acquire 2 a false, .acquire 3 a false, .dialed 0 ok,
    .dialed 1 ok, .released 1 true] ==
  ["dial 1 a #0", "dial 2 a #1", "grant 1 #0", "grant 2 #1", "grant 3 #1"]

-- Waiting requests are served oldest first.
#guard runTags [.acquire 1 a false, .acquire 2 a false, .acquire 3 a false, .acquire 4 a false,
    .dialed 0 ok, .dialed 1 ok, .released 0 true, .released 1 true] ==
  ["dial 1 a #0", "dial 2 a #1", "grant 1 #0", "grant 2 #1", "grant 3 #0", "grant 4 #1"]

-- A connection that closes passes its place to the oldest waiting request, which opens its own.
#guard runTags [.acquire 1 a false, .acquire 2 a false, .acquire 3 a false, .dialed 0 ok,
    .connectionClosed 0] ==
  ["dial 1 a #0", "dial 2 a #1", "grant 1 #0", "dial 3 a #2"]

-- So does a connection that fails to open, after failing its own request.
#guard runTags [.acquire 1 a false, .acquire 2 a false, .acquire 3 a false, .dialed 0 refused] ==
  ["dial 1 a #0", "dial 2 a #1", "reject 1: connect: refused", "dial 3 a #2"]

-- A connection being closed still counts: no request goes past the limit while it tears down.
#guard runTags [.acquire 1 a false, .acquire 2 a false, .dialed 0 ok, .dialed 1 ok,
    .released 0 false, .acquire 3 a false] ==
  ["dial 1 a #0", "dial 2 a #1", "grant 1 #0", "grant 2 #1", "close #0"]

-- Origins have separate limits.
#guard runTags [.acquire 1 a false, .acquire 2 a false, .acquire 3 b false] ==
  ["dial 1 a #0", "dial 2 a #1", "dial 3 b #2"]

/-! ## Retries -/

-- A fresh request skips idle connections while under the limit...
#guard runTags [.acquire 1 a false, .dialed 0 ok, .released 0 true, .acquire 2 a true] ==
  ["dial 1 a #0", "grant 1 #0", "dial 2 a #1"]

-- ...and at it closes the least recently used one, then waits for the place it frees.
#guard runTags [.acquire 1 a false, .acquire 2 a false, .dialed 0 ok, .dialed 1 ok,
    .released 0 true, .released 1 true, .acquire 3 a true, .connectionClosed 0] ==
  ["dial 1 a #0", "dial 2 a #1", "grant 1 #0", "grant 2 #1", "close #0", "dial 3 a #2"]

-- A connection told to close is never granted, even when released as reusable.
#guard
  let (s, cmds) := run [.acquire 1 a false, .acquire 2 a false, .dialed 0 ok, .dialed 1 ok,
    .released 1 true, .acquire 3 a true]
  tags cmds == ["dial 1 a #0", "dial 2 a #1", "grant 1 #0", "grant 2 #1", "close #1"] &&
    runTags [.released 1 true, .released 0 true] s == ["grant 3 #0"]

/-! ## Closing -/

#guard
  let (s, _) := run [.acquire 1 a false, .acquire 2 a false, .acquire 3 a false, .dialed 0 ok]
  let (s, cmds) := run [.close] s
  tags cmds == ["reject 3: client closed while the request waited for a connection",
    "reject 2: client closed while the connection was being opened", "close #0"] &&
    -- The cancelled dial is closed once it opens, and holds its place until then.
    runTags [.dialed 1 ok] s == ["close #1"] &&
    (run [.dialed 1 ok, .connectionClosed 0, .connectionClosed 1] s).1.pools.isEmpty

-- The pool is usable after `close`: a later request opens a fresh connection.
#guard
  let (s, _) := run [.acquire 1 a false, .dialed 0 ok, .released 0 true, .close]
  runTags [.acquire 2 a false] s == ["dial 2 a #1"]

-- A cancelled dial that fails answers nothing more.
#guard
  let (s, _) := run [.acquire 1 a false, .close]
  runTags [.dialed 0 refused] s == [] && (run [.dialed 0 refused] s).1.pools.isEmpty

/-! ## Every request is answered once -/

#guard
  let (s, cmds) := run [.acquire 1 a false, .acquire 2 a false, .acquire 3 a false,
    .acquire 4 a true, .acquire 5 b false, .dialed 0 refused, .dialed 2 ok, .dialed 1 ok,
    .released 1 true, .dialed 3 ok, .released 3 false, .connectionClosed 3, .close,
    .dialed 4 ok]
  let tickets := answered cmds
  tickets.length == 5 && [1, 2, 3, 4, 5].all tickets.contains && s.pools.all (·.waiters.isEmpty)

-- Inputs about unknown connections change nothing.
#guard runTags [.dialed 7 ok, .released 7 true, .retired 7, .connectionClosed 7] == [] &&
  (run [.dialed 7 ok, .released 7 true, .retired 7, .connectionClosed 7]).1.pools.isEmpty

/-! ## Origins -/

def originOf (u : String) : URI.Origin := (URI.parse! u).origin?.getD a

-- An origin is a scheme, a host and a port (RFC 6454 §4): each has its own connections, and the
-- default port is the same origin as none.
#guard runTags [.acquire 1 (originOf "http://a/") false, .dialed 0 ok, .released 0 true,
    .acquire 2 (originOf "http://a:8080/") false, .acquire 3 (originOf "https://a/") false,
    .acquire 4 (originOf "http://a:80/") false] ==
  ["dial 1 a #0", "grant 1 #0", "dial 2 a #1", "dial 3 a #2", "grant 4 #0"]

/-! ## More on the limit and retries -/

-- At the limit with every connection held, a fresh request waits: no held connection is closed.
#guard runTags [.acquire 1 a false, .acquire 2 a false, .dialed 0 ok, .dialed 1 ok, .acquire 3 a true] ==
  ["dial 1 a #0", "dial 2 a #1", "grant 1 #0", "grant 2 #1"]

-- A connection handed straight from its release to a waiting fresh request never sat idle, so it is
-- not one that may have gone stale: the fresh request takes it.
#guard runTags [.acquire 1 a false, .acquire 2 a false, .dialed 0 ok, .dialed 1 ok, .acquire 3 a true,
    .released 0 true] ==
  ["dial 1 a #0", "dial 2 a #1", "grant 1 #0", "grant 2 #1", "grant 3 #0"]

-- Waiting requests are served oldest first, fresh or not.
#guard
  let one : Client.Config := { maxConnectionsPerOrigin := ⟨1, by decide⟩ }
  tags (run [.acquire 1 a false, .dialed 0 ok, .acquire 2 a false, .acquire 3 a true, .released 0 true]
      (config := one)).2 == ["dial 1 a #0", "grant 1 #0", "grant 2 #0"] &&
    tags (run [.acquire 1 a false, .dialed 0 ok, .acquire 2 a true, .acquire 3 a false, .released 0 true]
      (config := one)).2 == ["dial 1 a #0", "grant 1 #0", "grant 2 #0"]

-- A connection whose release did not keep it waits for its loop to exit before its place is passed.
#guard runTags [.acquire 1 a false, .acquire 2 a false, .acquire 3 a false, .dialed 0 ok, .dialed 1 ok,
    .released 0 false, .connectionClosed 0] ==
  ["dial 1 a #0", "dial 2 a #1", "grant 1 #0", "grant 2 #1", "close #0", "dial 3 a #2"]

/-! ## Inputs reported twice -/

-- A connection released twice is granted once.
#guard runTags [.acquire 1 a false, .dialed 0 ok, .released 0 true, .released 0 true, .acquire 2 a false,
    .acquire 3 a false] ==
  ["dial 1 a #0", "grant 1 #0", "grant 2 #0", "dial 3 a #1"]

-- A connection reported open twice is granted once.
#guard runTags [.acquire 1 a false, .dialed 0 ok, .dialed 0 ok] == ["dial 1 a #0", "grant 1 #0"]

/-! ## More on closing -/

-- `close` closes idle connections too.
#guard runTags [.acquire 1 a false, .dialed 0 ok, .released 0 true, .close] ==
  ["dial 1 a #0", "grant 1 #0", "close #0"]

-- A connection released after `close` goes back to no one.
#guard
  let (s, _) := run [.acquire 1 a false, .dialed 0 ok, .close]
  runTags [.released 0 true, .acquire 2 a false] s == ["dial 2 a #1"]

-- Connection names are never reused, across `close` too.
#guard runTags [.acquire 1 a false, .dialed 0 ok, .close, .connectionClosed 0, .acquire 2 a false] ==
  ["dial 1 a #0", "grant 1 #0", "close #0", "dial 2 a #1"]
