import Std.Http

/-!
Tests the HTTP client driver (`Std.Http.Client.Driver`), the machine made of the hop, pool and
connection drivers, without I/O: a request to a new connection, redirects whose body the machine
reads itself (same origin, reusing the connection, and to another origin), cookies loaded before a
request and stored after its response, authentication challenges answered or handed to the caller,
and empty writes the machine answers itself.
-/

open Std.Http Std.Http.Client Std.Http.Client.Driver

/-- A command, as a line of the log. -/
def show1 : Command → String
  | .dial id o => s!"dial #{id} {o.host}"
  | .connection id (.write d) => s!"#{id} write {(String.fromUTF8! d.toByteArray).replace "\r\n" " | "}"
  | .connection id .awaitWritten => s!"#{id} awaitWritten"
  | .connection id .flush => s!"#{id} flush"
  | .connection id .close => s!"#{id} close"
  | .request t (.body .original) => s!"t{t} body original"
  | .request t (.body .rewound) => s!"t{t} body rewound"
  | .request t (.body .empty) => s!"t{t} body empty"
  | .request t (.respond h _) => s!"t{t} respond {h.status.toCode}"
  | .request t (.offerBody c _) => s!"t{t} offer {String.fromUTF8! c.data}"
  | .request t .endResponse => s!"t{t} endResponse"
  | .request t .closeRequestBody => s!"t{t} closeRequestBody"
  | .request t .complete => s!"t{t} complete"
  | .request t (.fail e) => s!"t{t} fail {e}"
  | .request t (.loadCookies o tg) => s!"t{t} loadCookies {o.host}{tg}"
  | .request t (.storeCookies _ _ _) => s!"t{t} storeCookies"
  | .request t (.authenticate c) => s!"t{t} authenticate {if c.kind == .server then "server" else "proxy"}"
  | .request t (.intercept o tg) => s!"t{t} intercept {o.host}{tg.uri}"
  | .request t (.observe _ _ h) => s!"t{t} observe {h.status.toCode}"
  | .request t (.informational _ _ h) => s!"t{t} informational {h.status.toCode}"
  | .request t (.trailers fs) => s!"t{t} trailers {fs.size}"

def writeOf : Command → Option ConnectionId
  | .connection id (.write _) => some id
  | .connection id .awaitWritten => some id
  | .connection id .flush => some id
  | _ => none

/--
A pure interpreter at time `now`: completes every write at once, steps again while the machine asks
to resume, and logs every command.
-/
partial def drive (cfg : Client.Config) (s : State) (cmds : Array Command) (log : Array String)
    (now : Nat := 0) : State × Array String :=
  let log := log ++ cmds.map show1
  match cmds.findSome? writeOf with
  | some id =>
    let (s, more) := step cfg s now (.connection id (.written true .idle))
    drive cfg s more log now
  | none =>
    if (wants cfg s now).resume then
      let (s, more) := step cfg s now .resume
      drive cfg s more log now
    else (s, log)

/--
Applies timed inputs in order; returns each input's log, the requests left, the connections and the
final state.
-/
def runTimed (cfg : Client.Config) (inputs : List (Nat × Input)) :
    List (List String) × Nat × Nat × State :=
  let (s, logs) := inputs.foldl (init := (({} : State), [])) fun (s, logs) (now, i) =>
    let (s, cmds) := step cfg s now i
    let (s, l) := drive cfg s cmds #[] now
    (s, logs ++ [l.toList])
  (logs, s.reqs.size, s.conns.size, s)

/-- Applies `inputs` in order; returns each input's log, the requests left and the connections. -/
def runAll (cfg : Client.Config) (inputs : List Input) : List (List String) × Nat × Nat :=
  let (logs, reqs, conns, _) := runTimed cfg (inputs.map (0, ·))
  (logs, reqs, conns)

def originOf (h : String) : URI.Origin :=
  (URI.parse! s!"http://{h}/").origin?.getD
    { scheme := URI.Scheme.ofString! "http", host := .empty, port := 0 }

def getA : Request.Head := { method := .get, version := .v11, uri := RequestTarget.parse! "/a" }

def submit : Input := .submit 1 (originOf "a") getA (some (.fixed 0)) {} true
def bytes (id : ConnectionId) (s : String) : Input := .connection id (.received (some s.toUTF8))
def getHead (path host : String) (extra : String := "") : String :=
  s!"#1 write GET {path} HTTP/1.1 | {extra}Host: {host} | User-Agent: lean-http/1.1 |  | "

/-! ## A request on a new connection -/

#guard runAll {} [submit, .dialed 1 (.ok ()), .request 1 (.pulled none),
    bytes 1 "HTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\nhi", .request 1 (.bodyInterest true)] ==
  ([["t1 body original", "dial #1 a"], [getHead "/a" "a"], ["t1 closeRequestBody"],
    ["t1 respond 200"], ["t1 offer hi", "t1 complete"]], 0, 1)

/-! ## Redirects -/

-- A same-origin redirect: its body, still arriving, is read and discarded by the machine, and the
-- next hop reuses the connection.
#guard runAll {} [submit, .dialed 1 (.ok ()), .request 1 (.pulled none),
    bytes 1 "HTTP/1.1 302 Found\r\nLocation: /b\r\nContent-Length: 6\r\n\r\nabc", bytes 1 "def",
    .request 1 (.pulled none), bytes 1 "HTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\nhi",
    .request 1 (.bodyInterest true)] ==
  ([["t1 body original", "dial #1 a"], [getHead "/a" "a"], ["t1 closeRequestBody"], [],
    ["t1 body empty", getHead "/b" "a"], ["t1 closeRequestBody"], ["t1 respond 200"],
    ["t1 offer hi", "t1 complete"]], 0, 1)

-- A redirect to another origin opens a connection there.
#guard
  let (logs, reqs, conns) := runAll {} [submit, .dialed 1 (.ok ()), .request 1 (.pulled none),
    bytes 1 "HTTP/1.1 302 Found\r\nLocation: http://b/x\r\nContent-Length: 0\r\n\r\n"]
  logs.getLast? == some ["t1 body empty", "dial #2 b"] && reqs == 1 && conns == 1

-- The caller never sees the body of a redirect the machine follows.
#guard
  let (logs, _, _) := runAll {} [submit, .dialed 1 (.ok ()), .request 1 (.pulled none),
    bytes 1 "HTTP/1.1 302 Found\r\nLocation: /b\r\nContent-Length: 6\r\n\r\nabcdef"]
  !(logs.flatten.any (·.startsWith "t1 offer")) && !(logs.flatten.any (·.startsWith "t1 respond"))

/-! ## Cookies -/

def jar : CookieHandler := { load := fun _ _ => pure #[], store := fun _ _ _ => pure () }

-- Loaded before the request goes, which waits for them; stored when the response head arrives.
#guard runAll { cookieHandler := some jar } [submit, .dialed 1 (.ok ()),
    .cookies 1 #[.ofString! "sid=1"], .request 1 (.pulled none),
    bytes 1 "HTTP/1.1 200 OK\r\nContent-Length: 0\r\n\r\n"] ==
  ([["t1 body original", "t1 loadCookies a/a", "dial #1 a"], [],
    [getHead "/a" "a" |>.replace "Host: a | " "Host: a | Cookie: sid=1 | "], ["t1 closeRequestBody"],
    ["t1 storeCookies", "t1 respond 200", "t1 complete"]], 0, 1)

/-! ## Authentication challenges -/

def auth : Authenticator := Authenticator.const (.ofString! "Basic eA==")

def challenge401 : String :=
  "HTTP/1.1 401 Unauthorized\r\nWWW-Authenticate: Basic\r\nContent-Length: 4\r\n\r\nnope"

-- Answered: the body is kept meanwhile, and the request is sent again on the same connection, with
-- its body rewound and the credential.
#guard runAll { authenticator := some auth } [submit, .dialed 1 (.ok ()), .request 1 (.pulled none),
    bytes 1 challenge401, .credential 1 (some (.ofString! "Basic eA==")), .request 1 (.pulled none),
    bytes 1 "HTTP/1.1 200 OK\r\nContent-Length: 0\r\n\r\n"] ==
  ([["t1 body original", "dial #1 a"], [getHead "/a" "a"], ["t1 closeRequestBody"],
    ["t1 authenticate server"], ["t1 body rewound", getHead "/a" "a" "Authorization: Basic eA== | "],
    ["t1 closeRequestBody"], ["t1 respond 200", "t1 complete"]], 0, 1)

-- Declined: the caller gets the challenge with the body the machine kept.
#guard (runAll { authenticator := some auth } [submit, .dialed 1 (.ok ()), .request 1 (.pulled none),
    bytes 1 challenge401, .credential 1 none]).1.getLast? ==
  some ["t1 respond 401", "t1 offer nope", "t1 complete"]

-- Without an authenticator the challenge is the caller's, its body read by the caller.
#guard (runAll {} [submit, .dialed 1 (.ok ()), .request 1 (.pulled none), bytes 1 challenge401]).1.getLast? ==
  some ["t1 respond 401"]

/-! ## Writes -/

-- The empty writes of a pass never reach the interpreter.
#guard
  let (logs, _, _) := runAll {} [submit, .dialed 1 (.ok ()), .request 1 (.pulled none),
    bytes 1 "HTTP/1.1 204 No Content\r\n\r\n"]
  logs.flatten.all fun l => !(l.startsWith "#1 write") || l.length > "#1 write ".length

/-! ## Timers -/

/-- Like `drive`, at time `now`. -/
partial def driveAt (cfg : Client.Config) (now : Nat) (s : State) (cmds : Array Command) : State :=
  match cmds.findSome? writeOf with
  | some id =>
    let (s, more) := step cfg s now (.connection id (.written true .idle))
    driveAt cfg now s more
  | none => s

/-- Applies timed inputs in order, then returns what the machine waits on at `now`. -/
def wantsAfter (cfg : Client.Config) (inputs : List (Nat × Input)) (now : Nat) : Wants :=
  let s := inputs.foldl (init := ({} : State)) fun s (t, i) =>
    let (s, cmds) := step cfg s t i
    driveAt cfg t s cmds
  wants cfg s now

-- A connection's keep-alive wait started when it went idle: inputs for another connection past
-- `keepAliveTimeout` do not restart it, so it is due.
#guard
  let submit2 : Input := .submit 2 (originOf "a") getA (some (.fixed 0)) {} true
  let w := wantsAfter {} [(0, submit), (0, .dialed 1 (.ok ())), (0, .request 1 (.pulled none)),
    (0, submit2), (0, .dialed 2 (.ok ())), (0, .request 2 (.pulled none)),
    (0, bytes 2 "HTTP/1.1 204 No Content\r\n\r\n"),
    (3000, bytes 1 "HTTP/1.1 200 OK\r\nContent-Length: 10\r\n\r\nab"), (5000, bytes 1 "cd")] 5000
  w.timer.map (fun (id, t, ms) => (id, t == .idle, ms)) == some (2, true, 0)

-- Before it is due, the wait reports the time left from when the connection went idle.
#guard
  let w := wantsAfter {} [(0, submit), (0, .dialed 1 (.ok ())), (0, .request 1 (.pulled none)),
    (1000, bytes 1 "HTTP/1.1 204 No Content\r\n\r\n")] 2500
  w.timer.map (fun (id, t, ms) => (id, t == .idle, ms)) == some (1, true, 2500)

/-! ## Every request is answered -/

-- A redirect body of many chunks, all in one read, is read to its end before the next hop goes:
-- the machine never stops with a connection owed an input.
#guard
  let body := String.join (List.replicate 200 "1\r\nx\r\n") ++ "0\r\n\r\n"
  let (logs, reqs, _) := runAll {} [submit, .dialed 1 (.ok ()), .request 1 (.pulled none),
    bytes 1 ("HTTP/1.1 302 Found\r\nLocation: /b\r\nTransfer-Encoding: chunked\r\n\r\n" ++ body)]
  logs.getLast? == some ["t1 body empty", getHead "/b" "a"] && reqs == 1

def quick : Client.Config := { responseTimeout := ⟨1000, by decide⟩ }

def submitAt (t : Nat) : Input := .submit t (originOf "a") getA (some (.fixed 0)) {} true

/-- The tickets whose response is due by `now`, with the milliseconds left. -/
def deadlineAt (cfg : Client.Config) (s : State) (now : Nat) : Option (Ticket × Nat) :=
  (wants cfg s now).deadline

-- A request waiting for a connection held by a response that keeps streaming fails once its
-- response is overdue, and the stream goes on.
#guard
  let cfg := { quick with maxConnectionsPerOrigin := ⟨1, by decide⟩ }
  let chunk : Input := bytes 1 "1\r\nx\r\n"
  let (logs, _, _, s) := runTimed cfg [(0, submit), (0, .dialed 1 (.ok ())),
    (0, .request 1 (.pulled none)),
    (10, bytes 1 "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n"), (20, submitAt 2),
    (500, .request 1 (.bodyInterest true)), (600, chunk), (1000, .request 1 (.bodyInterest true)),
    (1019, chunk)]
  let due := deadlineAt cfg s 1020
  let (logs2, reqs, conns, _) := runTimed cfg [(0, submit), (0, .dialed 1 (.ok ())),
    (0, .request 1 (.pulled none)),
    (10, bytes 1 "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n"), (20, submitAt 2),
    (1020, .expired 2)]
  !(logs.flatten.any fun l => l.startsWith "t2 fail" || l.startsWith "t2 respond" || l.startsWith "dial #2") &&
    due == some (2, 0) &&
    logs2.getLast? == some ["t2 fail request timeout"] && reqs == 1 && conns == 1

-- The response of an answered request is never overdue: the deadline ends at `respond`.
#guard
  let (_, _, _, s) := runTimed quick [(0, submit), (0, .dialed 1 (.ok ())),
    (0, .request 1 (.pulled none)), (10, bytes 1 "HTTP/1.1 200 OK\r\nContent-Length: 4\r\n\r\nab")]
  deadlineAt quick s 5000 == none

-- An authenticator that never answers: the request fails when its response is overdue. The
-- challenge's exchange had ended, so its connection stays in the pool.
#guard
  let (logs, reqs, conns, _) := runTimed { quick with authenticator := some auth } [(0, submit),
    (0, .dialed 1 (.ok ())), (0, .request 1 (.pulled none)), (10, bytes 1 challenge401),
    (1000, .expired 1)]
  logs.getLast? == some ["t1 fail request timeout"] && reqs == 0 && conns == 1

-- The same while the challenge's body is still arriving: its connection closes.
#guard
  let (logs, reqs, conns, _) := runTimed { quick with authenticator := some auth } [(0, submit),
    (0, .dialed 1 (.ok ())), (0, .request 1 (.pulled none)),
    (10, bytes 1 "HTTP/1.1 401 Unauthorized\r\nWWW-Authenticate: Basic\r\nContent-Length: 10\r\n\r\nnope"),
    (1000, .expired 1)]
  logs.getLast? == some ["t1 fail request timeout", "#1 flush", "#1 close"] && reqs == 0 && conns == 0

-- A connection granted to a request that already failed goes back to the pool, and the next
-- request reuses it.
#guard
  let cfg := { quick with maxConnectionsPerOrigin := ⟨1, by decide⟩ }
  let (logs, reqs, conns, _) := runTimed cfg [(0, submit), (0, .dialed 1 (.ok ())),
    (0, .request 1 (.pulled none)), (20, submitAt 2), (1020, .expired 2),
    (1030, bytes 1 "HTTP/1.1 200 OK\r\nContent-Length: 0\r\n\r\n"), (1040, submitAt 3)]
  logs.getLast? == some ["t3 body original", "#1 write GET /a HTTP/1.1 | Host: a | User-Agent: lean-http/1.1 |  | "] &&
    reqs == 1 && conns == 1

-- Expiry of a ticket already answered, or unknown, does nothing.
#guard
  let (logs, reqs, _, _) := runTimed quick [(0, submit), (0, .dialed 1 (.ok ())),
    (0, .request 1 (.pulled none)),
    (10, bytes 1 "HTTP/1.1 200 OK\r\nContent-Length: 0\r\n\r\n"), (2000, .expired 1),
    (2000, .expired 7)]
  logs.drop 4 == [[], []] && reqs == 0

/-! ## Closing and cancelling -/

-- `close` fails the request in flight and the one waiting, and no retry opens a connection again.
#guard
  let cfg : Client.Config := { maxConnectionsPerOrigin := ⟨1, by decide⟩ }
  let (logs, reqs, conns, _) := runTimed cfg [(0, submit), (0, .dialed 1 (.ok ())),
    (0, .request 1 (.pulled none)), (10, submitAt 2), (20, .close)]
  let all := logs.flatten
  all.any (·.startsWith "t1 fail") && all.any (·.startsWith "t2 fail") &&
    !(all.any (·.startsWith "dial #2")) && reqs == 0 && conns == 0

-- A request submitted after `close` goes through as usual.
#guard
  let (logs, _, _, _) := runTimed {} [(0, submit), (0, .dialed 1 (.ok ())),
    (0, .request 1 (.pulled none)), (10, .close), (20, submitAt 2)]
  logs.getLast? == some ["t2 body original", "dial #2 a"]

-- `cancel` fails a request wherever it is with the given error, and frees what it held: here the
-- connection being opened for it, which the next request reuses.
#guard
  let (logs, reqs, conns, _) := runTimed {} [(0, submit), (0, .cancel 1 (.closed "rewind failed")),
    (5, .dialed 1 (.ok ())), (10, submitAt 2)]
  logs[1]? == some ["t1 fail " ++ toString (Client.Error.closed "rewind failed")] &&
    logs.getLast? == some ["t2 body original", getHead "/a" "a"] && reqs == 1 && conns == 1

-- Cancelled once its request was sent, the connection carrying it closes.
#guard
  let (logs, reqs, conns, _) := runTimed {} [(0, submit), (0, .dialed 1 (.ok ())),
    (0, .request 1 (.pulled none)), (10, .cancel 1 (.closed "abandoned"))]
  logs.getLast? == some ["t1 fail " ++ toString (Client.Error.closed "abandoned"), "#1 flush", "#1 close"] &&
    reqs == 0 && conns == 0

-- `cancel` after the response went to the caller does nothing.
#guard
  let (logs, _, _, _) := runTimed {} [(0, submit), (0, .dialed 1 (.ok ())),
    (0, .request 1 (.pulled none)), (10, bytes 1 "HTTP/1.1 200 OK\r\nContent-Length: 4\r\n\r\nab"),
    (20, .cancel 1 (.closed "late"))]
  logs.getLast? == some []
