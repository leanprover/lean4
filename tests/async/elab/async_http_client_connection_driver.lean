import Std.Http

/-!
Tests the HTTP client connection driver (`Std.Http.Client.Connection.Driver`) without I/O: a request's exchange
from submission to completion, keep-alive reuse, what the interpreter waits on, `Expect:
100-continue`, early and interim responses, bytes that answer no request, timeouts, the response
body limit, a response body the caller closes, write and request-body failures, and a request head
the machine refuses; then the framing of request and response bodies on the wire, when a connection
stops being reused, how its timers are armed, and the size of its reads.
-/

open Std.Http Std.Http.Client Std.Http.Client.Connection.Driver

def cfg : Client.Config := {}

def fresh (config : Client.Config := cfg) : State :=
  init { config := config.toH1Config }

def request (method : Method) (headers : Headers := .empty) : Request.Head :=
  { method, version := .v11, uri := RequestTarget.parse! "/",
    headers := headers.insert .host (.mk "a") }

/-- The decisions among `cmds`, without the writes. -/
def tags (cmds : Array Command) : List String :=
  cmds.toList.filterMap fun
    | .write _ | .awaitWritten | .flush => none
    | .deliverHead head _ => some s!"head {head.status.toCode}"
    | .offerBody chunk final =>
      some s!"body {String.fromUTF8! chunk.data}{if final then " final" else ""}"
    | .endResponse => some "endResponse"
    | .closeRequestBody => some "closeRequestBody"
    | .complete => some "complete"
    | .reject err => some s!"reject {err}"
    | .refuse err => some s!"refuse {err}"
    | .stopAccepting => some "stopAccepting"
    | .close => some "close"

/-- The bytes written by `cmds`. -/
def written (cmds : Array Command) : String :=
  String.fromUTF8! <| cmds.foldl (init := ByteArray.empty) fun out cmd =>
    match cmd with
    | .write data => out ++ data.toByteArray
    | _ => out

/--
Steps the driver until it waits on its sources or closes: a write batch is answered with `written
writesOk .idle`, a running stage with `resume`.
-/
def settle (config : Client.Config) (now : Nat) (writesOk : Bool) :
    Nat → State × Array Command → State × Array Command
  | 0, result => result
  | fuel + 1, (s, cmds) =>
    match s.stage with
    | .writing .. | .flushing =>
      let (s, more) := step config s now (.written writesOk .idle)
      settle config now writesOk fuel (s, cmds ++ more)
    | .running =>
      let (s, more) := step config s now .resume
      settle config now writesOk fuel (s, cmds ++ more)
    | .polling | .closed => (s, cmds)

/-- Applies `input` at `now` and settles. -/
def run (s : State) (input : Input) (now : Nat := 0) (config : Client.Config := cfg)
    (writesOk : Bool := true) : State × Array Command :=
  settle config now writesOk 64 (step config s now input)

def started (config : Client.Config := cfg) : State := (run (fresh config) .resume (config := config)).1

def submit (s : State) (head : Request.Head) (size : Option Body.Length := none)
    (config : Client.Config := cfg) : State × Array Command :=
  run s (.submit head size {}) (config := config)

def receive (s : State) (data : String) (config : Client.Config := cfg) : State × Array Command :=
  run s (.received (some data.toUTF8)) (config := config)

/-- A GET written whole: its request body ended at once. -/
def sentGet (config : Client.Config := cfg) : State :=
  let (s, _) := submit (started config) (request .get) (some (.fixed 0)) config
  (run s (.pulled none) (config := config)).1

/-! ## An exchange -/

#guard (started).waits && (started).idle

#guard
  let (s, cmds) := submit started (request .get) (some (.fixed 0))
  written cmds == "GET / HTTP/1.1\r\nHost: a\r\nUser-Agent: lean-http/1.1\r\n\r\n" && !s.idle

#guard
  let (s, cmds) := receive sentGet "HTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\nhi"
  let (s, more) := run s (.bodyInterest true)
  tags cmds == ["head 200"] && tags more == ["body hi final", "complete"] && s.idle

-- The connection is reused for the next request.
#guard
  let (s, _) := receive sentGet "HTTP/1.1 204 No Content\r\n\r\n"
  let (s, cmds) := submit s (request .get) (some (.fixed 0))
  written cmds == "GET / HTTP/1.1\r\nHost: a\r\nUser-Agent: lean-http/1.1\r\n\r\n" && !s.idle

-- A response to HEAD has no content, whatever its `Content-Length` says.
#guard
  let (s, _) := submit started (request .head) (some (.fixed 0))
  let (s, _) := run s (.pulled none)
  let (_, cmds) := receive s "HTTP/1.1 200 OK\r\nContent-Length: 50\r\n\r\n"
  cmds.any fun | .deliverHead _ size => size == some (.fixed 0) | _ => false

/-! ## What the interpreter waits on -/

#guard
  let src := sources cfg started
  src.request && src.recv.isSome && src.timers.map (·.1) == #[.idle] && !src.requestBody

#guard
  let (s, _) := submit started (request .post) none
  let src := sources cfg s
  !src.request && src.requestBody && src.timers.any (·.1 == .request)

-- Writes that pile up stop the request body, until they complete.
#guard
  let (s, _) := submit started (request .post) none
  let src := sources cfg { s with writes := .backlogged }
  !src.requestBody && src.writesIdle

-- While the caller has body bytes to take, `readTimeout` does not run: the caller is the one pausing.
#guard
  let (s, _) := receive sentGet "HTTP/1.1 200 OK\r\nContent-Length: 10\r\n\r\nhello"
  let src := sources cfg s
  src.responseInterest && !src.timers.any (·.1 == .read)

/-! ## `Expect: 100-continue` -/

def expectPost : Request.Head :=
  request .post (Headers.empty.insert .expect (.mk "100-continue"))

-- The body is parked until `100 Continue`, under the continue timer.
#guard
  let (s, _) := submit started expectPost none
  let src := sources cfg s
  !src.requestBody && src.timers.any (·.1 == .continue) &&
    (sources cfg (receive s "HTTP/1.1 100 Continue\r\n\r\n").1).requestBody

-- Or until the wait is over.
#guard
  let (s, _) := submit started expectPost none
  (sources cfg (run s (.fired .continue)).1).requestBody

-- A final response instead abandons the body.
#guard
  let (s, _) := submit started expectPost none
  let (_, cmds) := receive s "HTTP/1.1 417 Expectation Failed\r\nContent-Length: 0\r\n\r\n"
  -- The parked body was never framed, so the connection is not reused.
  tags cmds == ["closeRequestBody", "head 417", "stopAccepting", "complete", "close"]

-- The end of a body reported while it is parked clears the continue deadline too: left set, it would
-- end every wait at once.
#guard
  let (s, _) := submit started expectPost none
  let (s, _) := run s (.pulled none)
  !(sources cfg s).timers.any (·.1 == .continue)

-- The continue timer firing disarms it.
#guard
  let (s, _) := submit started expectPost none
  let (s, _) := run s (.fired .continue)
  !(sources cfg s).timers.any (·.1 == .continue)

/-! ## Interim responses -/

#guard
  let flood := String.join (List.replicate 17 "HTTP/1.1 103 Early Hints\r\n\r\n")
  let (s, cmds) := receive sentGet flood
  tags cmds == ["stopAccepting", "reject Other error: too many interim responses", "close"] && s.isClosed

/-! ## Bytes that answer no request -/

-- On an idle connection, as the `408` a server sends before closing it.
#guard
  let (s, cmds) := receive started "HTTP/1.1 408 Request Timeout\r\n\r\n"
  tags cmds == ["stopAccepting", "close"] && s.isClosed

-- Before the request head was written: the request never left, so it may be sent again.
#guard
  let (s, _) := submit started (request .post) none
  let (s, cmds) := receive s "HTTP/1.1 200 OK\r\nContent-Length: 0\r\n\r\n"
  tags cmds == ["stopAccepting", "reject the peer sent a response before the request was written", "close"] &&
    s.isClosed

#guard
  let (s, _) := submit started (request .post) none
  let (_, cmds) := run s (.received none)
  tags cmds == ["stopAccepting", "reject connection closed before the request was written", "close"]

/-! ## Timeouts and shutdown -/

#guard tags (run started (.fired .idle)).2 == ["stopAccepting", "close"]
#guard tags (run sentGet (.fired .request)).2 == ["stopAccepting", "reject request timeout", "close"]
#guard tags (run sentGet (.fired .read)).2 == ["stopAccepting", "reject request timeout", "close"]
#guard tags (run sentGet .cancelled).2 == ["stopAccepting", "reject connection shutdown", "close"]

-- The request deadline moves with each response chunk the caller takes.
#guard
  let (s, _) := receive sentGet "HTTP/1.1 200 OK\r\nContent-Length: 4\r\n\r\nab"
  let (s, _) := run s (.bodyInterest true) (now := 100000)
  s.exchange.any (·.deadline == 100000 + 120000)

/-! ## Writes in flight -/

-- While a write is in flight the wait is on the peer taking the bytes: `readTimeout` does not run,
-- and a stalled write, not `requestTimeout` as a whole, bounds it.
#guard
  let src := sources cfg { sentGet with writes := .inFlight }
  !src.timers.any (·.1 == .read) && src.writesIdle && src.writesLate &&
    !src.timers.any (·.1 == .request)

-- A response that ends its exchange reaches the caller before the exchange waits for its writes.
#guard
  let s := { sentGet with writes := .inFlight }
  let (s, _) := step cfg s 0 (.received (some "HTTP/1.1 204 No Content\r\n\r\n".toUTF8))
  let (s, cmds) := step cfg s 0 (.written true .inFlight)
  let (s, more) := step cfg s 0 (.written true .idle)
  -- The response ended at its head, so it is whole and closed before the wait.
  tags cmds == ["head 204", "endResponse"] && cmds.back? matches some .awaitWritten &&
    tags more == ["complete"] && s.idle

-- A response the caller holds whole is closed before the exchange waits for its writes.
#guard
  let s := { sentGet with writes := .inFlight }
  let (s, _) := step cfg s 0 (.received (some "HTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\nok".toUTF8))
  let (s, _) := step cfg s 0 (.written true .inFlight)
  let (s, offered) := step cfg s 0 (.bodyInterest true)
  let (s, cmds) := step cfg s 0 (.written true .inFlight)
  tags offered == ["body ok final"] && tags cmds == ["endResponse"] &&
    cmds.back? matches some .awaitWritten && tags (step cfg s 0 (.written true .idle)).2 == ["complete"]

-- A connection that ends inside a response fails the exchange as closed, once the caller has the
-- bytes that came before.
#guard
  let (s, _) := receive sentGet "HTTP/1.1 200 OK\r\nContent-Length: 10\r\n\r\nab"
  let (s, _) := run s (.received none)
  let (s, delivered) := run s (.bodyInterest true)
  tags delivered == ["body ab"] &&
    tags (run s (.bodyInterest true)).2 == ["stopAccepting", "reject connection closed", "close"]

/-! ## Response body -/

-- Past `maxResponseBodySize`, the exchange fails.
#guard
  let small : Client.Config := { maxResponseBodySize := some 3 }
  let (s, _) := receive (sentGet small) "HTTP/1.1 200 OK\r\nContent-Length: 10\r\n\r\n0123456789" small
  let (s, cmds) := run s (.bodyInterest true) (config := small)
  tags cmds == ["stopAccepting", "reject response body exceeds maximum allowed size", "close"] && s.isClosed

-- A body the caller closes is drained when the machine holds the rest of it...
#guard
  let (s, _) := receive sentGet "HTTP/1.1 200 OK\r\nContent-Length: 4\r\n\r\nabcd"
  let (s, cmds) := run s (.bodyInterest false)
  tags cmds == ["complete"] && s.idle

-- ...and ends the connection when the rest is still to arrive.
#guard
  let (s, _) := receive sentGet "HTTP/1.1 200 OK\r\nContent-Length: 10\r\n\r\nabcd"
  let (s, cmds) := run s (.bodyInterest false)
  tags cmds == ["stopAccepting", "reject response body closed before it ended", "close"] && s.isClosed

-- While the request body is still produced, a finished response body is closed at once.
#guard
  let (s, _) := submit started (request .post (Headers.empty.insert .contentLength (.mk "4"))) (some (.fixed 4))
  let (s, _) := run s (.pulled (some (Chunk.ofByteArray "ab".toUTF8)))
  let (s, _) := receive s "HTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\nok"
  let (_, cmds) := run s (.bodyInterest true)
  tags cmds == ["body ok final", "endResponse"]

-- Bytes past the end of a response end the connection, but the caller has the whole response, so
-- the exchange completes.
#guard
  let (s, cmds) := receive sentGet "HTTP/1.1 204 No Content\r\n\r\nHTTP/1.1 200 OK\r\n\r\n"
  tags cmds == ["head 204", "stopAccepting", "complete", "close"] && s.isClosed

/-! ## Failures -/

-- A write that fails before the response fails the exchange.
#guard
  let (s, _) := submit started (request .get) (some (.fixed 0))
  let (s, cmds) := run s (.pulled none) (writesOk := false)
  (tags cmds).contains "reject connection write failed" && s.isClosed

-- A request body that raises fails the exchange as the caller's, and ends the message unframed.
#guard
  let (s, _) := submit started (request .post) none
  let (s, cmds) := run s (.pullFailed (.userError "boom"))
  tags cmds == ["closeRequestBody", "stopAccepting", "reject boom", "close"] && s.isClosed

-- A head the machine refuses never starts an exchange.
#guard
  let noHost : Request.Head := { method := .get, version := .v11, uri := RequestTarget.parse! "/" }
  let (s, cmds) := submit started noHost (some (.fixed 0))
  (tags cmds).head? == some "refuse the HTTP/1.1 request has no Host field" &&
    (tags cmds).contains "close" && s.isClosed && written cmds == ""

/-! ## A closed connection -/

#guard
  let (s, _) := run started .cancelled
  s.isClosed && (step cfg s 0 .resume).2.isEmpty

/-! ## Request framing -/

def postWithLength (n : Nat) : Request.Head :=
  request .post (Headers.empty.insert .contentLength (.ofString! (toString n)))

def pull (s : State) (data : String) : State × Array Command :=
  run s (.pulled (some (Chunk.ofByteArray data.toUTF8)))

-- A body of known length goes out as it is, after the head that declares it.
#guard
  let (s, head) := submit started (postWithLength 4) (some (.fixed 4))
  let (s, _) := pull s "abcd"
  let (_, last) := run s (.pulled none)
  written head == "POST / HTTP/1.1\r\nHost: a\r\nUser-Agent: lean-http/1.1\r\nContent-Length: 4\r\n\r\n" &&
    written last == "abcd" && tags last == ["closeRequestBody"]

-- A body of unknown length is chunked (RFC 9112 §7.1), and ends with the last chunk.
#guard
  let (s, _) := submit started (request .post) none
  let (s, first) := pull s "abcd"
  let (_, last) := run s (.pulled none)
  written first ==
      "POST / HTTP/1.1\r\nHost: a\r\nUser-Agent: lean-http/1.1\r\nTransfer-Encoding: chunked\r\n\r\n4\r\nabcd\r\n" &&
    written last == "0\r\n\r\n"

-- A body that ends short of its `Content-Length` fails the request as the caller's: the peer would
-- wait for the rest. The message cannot be framed anymore, so the connection ends.
#guard
  let (s, _) := submit started (postWithLength 4) (some (.fixed 4))
  let (s, _) := pull s "ab"
  let (s, cmds) := run s (.pulled none)
  cmds.any (fun | .reject (.invalidRequest msg) => msg == "the request body ended 2 bytes short of its length"
                 | _ => false) &&
    (tags cmds).contains "closeRequestBody" && s.isClosed

-- An HTTP/1.0 request asks for the connection to close, and the connection ends after its response.
#guard
  let (s, head) := submit started { request .get with version := .v10 } (some (.fixed 0))
  let (s, _) := run s (.pulled none)
  let (s, cmds) := receive s "HTTP/1.1 200 OK\r\nContent-Length: 0\r\n\r\n"
  (written head).endsWith "Connection: close\r\n\r\n" && tags cmds == ["head 200", "complete", "close"] &&
    s.isClosed

/-! ## Response framing -/

-- A chunked body reaches the caller chunk by chunk, across reads, and ends at its last chunk.
#guard
  let (s, head) := receive sentGet "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n2\r\nab\r\n"
  let (s, first) := run s (.bodyInterest true)
  let (s, _) := receive s "1\r\nc\r\n0\r\n\r\n"
  let (s, second) := run s (.bodyInterest true)
  let (s, last) := run s (.bodyInterest true)
  tags head == ["head 200"] && tags first == ["body ab"] && tags second == ["body c"] &&
    (tags last).getLast? == some "complete" && s.idle

-- A head split across reads is delivered once it is whole.
#guard
  let (s, first) := receive sentGet "HTTP/1.1 200 OK\r\nContent-Le"
  let (s, second) := receive s "ngth: 0\r\n\r\n"
  tags first == [] && tags second == ["head 200", "complete"] && s.idle

-- A body with neither `Content-Length` nor `Transfer-Encoding` runs until the peer closes
-- (RFC 9112 §6.3), so the connection is not reused.
#guard
  let (s, head) := receive sentGet "HTTP/1.1 200 OK\r\n\r\nabc"
  let (s, first) := run s (.bodyInterest true)
  let (s, _) := run s (.received none)
  let (s, last) := run s (.bodyInterest true)
  tags head == ["head 200", "stopAccepting"] && tags first == ["body abc"] &&
    (tags last).contains "complete" && (tags last).getLast? == some "close" && s.isClosed

-- A `304` has no content, whatever its `Content-Length` says (RFC 9110 §15.4.5).
#guard tags (receive sentGet "HTTP/1.1 304 Not Modified\r\nContent-Length: 10\r\n\r\n").2 ==
  ["head 304", "complete"]

-- Conflicting `Content-Length` values are an unrecoverable error (RFC 9112 §6.3).
#guard
  let (s, cmds) := receive sentGet "HTTP/1.1 200 OK\r\nContent-Length: 2\r\nContent-Length: 3\r\n\r\nhi"
  !(tags cmds).any (·.startsWith "head") && (tags cmds).any (·.startsWith "reject") && s.isClosed

-- Both `Transfer-Encoding` and `Content-Length` may mean response splitting (RFC 9112 §6.3).
#guard
  let (s, cmds) :=
    receive sentGet "HTTP/1.1 200 OK\r\nContent-Length: 2\r\nTransfer-Encoding: chunked\r\n\r\n0\r\n\r\n"
  !(tags cmds).any (·.startsWith "head") && (tags cmds).any (·.startsWith "reject") && s.isClosed

-- An interim response under the limit is skipped, and the final one follows.
#guard tags (receive sentGet
    "HTTP/1.1 103 Early Hints\r\nLink: </a>\r\n\r\nHTTP/1.1 204 No Content\r\n\r\n").2 ==
  ["head 204", "complete"]

/-! ## Reuse -/

-- `Connection: close` ends the connection once the response is whole (RFC 9112 §9.6).
#guard
  let (s, head) := receive sentGet "HTTP/1.1 200 OK\r\nConnection: close\r\nContent-Length: 2\r\n\r\nhi"
  let (s, rest) := run s (.bodyInterest true)
  tags head == ["head 200", "stopAccepting"] && tags rest == ["body hi final", "complete", "close"] &&
    s.isClosed

-- So does an HTTP/1.0 response, which does not keep the connection alive by default (RFC 9112 §9.3).
#guard
  let (s, head) := receive sentGet "HTTP/1.0 200 OK\r\nContent-Length: 2\r\n\r\nhi"
  let (s, rest) := run s (.bodyInterest true)
  tags head == ["head 200", "stopAccepting"] && (tags rest).getLast? == some "close" && s.isClosed

-- And the last request `maxRequests` allows.
#guard
  let one : Client.Config := { maxRequests := 1 }
  let (s, cmds) := receive (sentGet one) "HTTP/1.1 204 No Content\r\n\r\n" one
  tags cmds == ["head 204", "complete", "close"] && s.isClosed

-- A connection that carries a request takes no other.
#guard tags (submit sentGet (request .get) (some (.fixed 0))).2 == ["refuse the connection takes no request now"]

-- The peer closing an idle connection ends it quietly.
#guard
  let (s, _) := receive sentGet "HTTP/1.1 204 No Content\r\n\r\n"
  let (s, cmds) := run s (.received none)
  tags cmds == ["stopAccepting", "close"] && s.isClosed

/-! ## Timers -/

-- Idle, the connection waits `keepAliveTimeout` from when the wait starts.
#guard (sources cfg started).timers == #[(.idle, .within 4000)]

-- Back to idle after an exchange, the keep-alive wait is armed again.
#guard
  let (s, _) := receive sentGet "HTTP/1.1 200 OK\r\nContent-Length: 2\r\nX: y\r\n\r\nhi"
  let (s, _) := run s (.bodyInterest true)
  s.idle && (sources cfg s).timers == #[(.idle, .within 4000)]

-- Waiting for the head, a read waits `readTimeout`, and the exchange its deadline.
#guard (sources cfg sentGet).timers == #[(.read, .within 30000), (.request, .until 120000)]

-- While the request body is produced, the caller is the one pausing: no read timeout.
#guard
  let (s, _) := submit started (request .post) none
  (sources cfg s).timers == #[(.request, .until 120000)]

-- The deadline is `requestTimeout` from the submission, or the request's own override.
#guard
  let deadline (s : State) := s.exchange.map fun (e : Exchange) => e.deadline
  let plain := (run started (.submit (request .get) (some (.fixed 0)) {}) (now := 1000)).1
  let short := (run started (.submit (request .get) (some (.fixed 0))
    { requestTimeout := some ⟨500, by decide⟩ }) (now := 1000)).1
  deadline plain == some 121000 && deadline short == some 1500

-- Writes completing are progress: the deadline moves, and the writes are idle again.
#guard
  let (s, _) := run { sentGet with writes := .inFlight } .writesIdle (now := 5000)
  s.writes == .idle && s.exchange.any (·.deadline == 125000)

/-! ## Write failures while waiting -/

-- After the final head, a failed write abandons the request body: the response stands, and the
-- exchange completes, but the connection ends.
#guard
  let (s, _) := submit started (postWithLength 4) (some (.fixed 4))
  let (s, _) := pull s "ab"
  let (s, head) := receive s "HTTP/1.1 413 Content Too Large\r\nContent-Length: 0\r\n\r\n"
  let (s, cmds) := run s (.written false .idle)
  (tags head).head? == some "head 413" &&
    tags cmds == ["stopAccepting", "closeRequestBody", "complete", "close"] && s.isClosed

-- Before it, the exchange fails.
#guard
  let (s, _) := submit started (request .post) none
  let (s, cmds) := run s (.written false .idle)
  tags cmds == ["stopAccepting", "reject connection write failed", "close"] && s.isClosed

-- A read that fails ends the exchange with the error.
#guard tags (run sentGet (.failed (.userError "reset"))).2 ==
  ["stopAccepting", "reject connection read failed: reset", "close"]

/-! ## Reads -/

-- No read asks for more than `maximumRecvSize`, idle or not.
#guard
  let small : Client.Config := { maximumRecvSize := 100, defaultPayloadBytes := 4096 }
  (sources small (started small)).recv == some 100 && (sources small (sentGet small)).recv == some 100

/-! ## RFC 9112 and RFC 9110 requirements -/

/-- The decisions taken on `data` received after a GET was sent, and whether the connection closed. -/
def answer (data : String) : List String × Bool :=
  let (s, cmds) := receive sentGet data
  (tags cmds, s.isClosed)

/-- The head the caller got, if any. -/
def headOf (cmds : Array Command) : Option Response.Head :=
  cmds.toList.findSome? fun | .deliverHead head _ => some head | _ => none

-- A `204` has no content, whatever its `Content-Length` says (RFC 9112 §6.3).
#guard answer "HTTP/1.1 204 No Content\r\nContent-Length: 5\r\n\r\n" == (["head 204", "complete"], false)

-- So has a response to HEAD, even one that says it is chunked (RFC 9112 §6.3).
#guard
  let (s, _) := submit started (request .head) (some (.fixed 0))
  let (s, _) := run s (.pulled none)
  tags (receive s "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n").2 == ["head 200", "complete"]

-- An invalid `Content-Length` is an unrecoverable error (RFC 9112 §6.3).
#guard
  let (t, closed) := answer "HTTP/1.1 200 OK\r\nContent-Length: abc\r\n\r\n"
  !t.any (·.startsWith "head") && t.any (·.startsWith "reject") && closed

-- A `Transfer-Encoding` whose last coding is not `chunked` runs until the peer closes (RFC 9112 §6.3).
#guard
  let (s, cmds) := receive sentGet "HTTP/1.1 200 OK\r\nTransfer-Encoding: gzip\r\n\r\nxyz"
  tags cmds == ["head 200", "stopAccepting"] && !s.idle
#guard
  let (s, cmds) := receive sentGet "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked, gzip\r\n\r\nxyz"
  tags cmds == ["head 200", "stopAccepting"] && !s.idle

-- Chunk extensions are ignored (RFC 9112 §7.1.1), and trailer fields are not content (§7.1.2).
#guard
  let (s, _) := receive sentGet "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n2;ext=1\r\nab\r\n0\r\n\r\n"
  let (s, first) := run s (.bodyInterest true)
  let (s, last) := run s (.bodyInterest true)
  tags first == ["body ab"] && (tags last).getLast? == some "complete" && s.idle
#guard
  let (s, _) := receive sentGet "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n2\r\nab\r\n0\r\nX-T: 1\r\n\r\n"
  let (s, first) := run s (.bodyInterest true)
  let (s, last) := run s (.bodyInterest true)
  tags first == ["body ab"] && !(tags last).any (·.startsWith "body X") &&
    (tags last).getLast? == some "complete" && s.idle

-- A chunk size that is not hexadecimal fails the exchange (RFC 9112 §7.1).
#guard
  let (s, _) := receive sentGet "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\nzz\r\n"
  let (s, cmds) := run s (.bodyInterest true)
  (tags cmds).any (·.startsWith "reject") && s.isClosed

-- A user agent replaces an obsolete line folding with spaces (RFC 9112 §5.2).
#guard
  let (_, cmds) := receive sentGet "HTTP/1.1 200 OK\r\nX: a\r\n b\r\nContent-Length: 0\r\n\r\n"
  (headOf cmds).any fun head => (head.headers.get? (Header.Name.ofString! "x")).any (·.value == "a b")

-- The reason phrase may be empty (RFC 9112 §4).
#guard answer "HTTP/1.1 200 \r\nContent-Length: 0\r\n\r\n" == (["head 200", "complete"], false)

-- A major version other than 1 is not HTTP/1.1 (RFC 9112 §2.3).
#guard
  let (t, closed) := answer "HTTP/2.0 200 OK\r\nContent-Length: 0\r\n\r\n"
  !t.any (·.startsWith "head") && t.any (·.startsWith "reject") && closed

-- More header fields than `maxHeaders` fail the exchange.
#guard
  let few : Client.Config := { maxHeaders := 2 }
  let (s, cmds) := receive (sentGet few) "HTTP/1.1 200 OK\r\nA: 1\r\nB: 2\r\nC: 3\r\nContent-Length: 0\r\n\r\n" few
  !(tags cmds).any (·.startsWith "head") && (tags cmds).any (·.startsWith "reject") && s.isClosed

-- After a `101`, the connection speaks another protocol: it is not reused (RFC 9110 §15.2.2).
#guard
  let (t, closed) := answer "HTTP/1.1 101 Switching Protocols\r\nUpgrade: x\r\nConnection: upgrade\r\n\r\n"
  t.head? == some "head 101" && t.getLast? == some "close" && closed

-- A request that asks to close the connection closes it after the response (RFC 9112 §9.6).
#guard
  let (s, _) := submit started (request .get (Headers.empty.insert .connection (.mk "close"))) (some (.fixed 0))
  let (s, _) := run s (.pulled none)
  let (s, cmds) := receive s "HTTP/1.1 200 OK\r\nContent-Length: 0\r\n\r\n"
  tags cmds == ["head 200", "complete", "close"] && s.isClosed

-- A request without content carries no `100-continue` expectation and does not wait for one
-- (RFC 9110 §10.1.1).
#guard
  let (s, cmds) := submit started (request .get (Headers.empty.insert .expect (.mk "100-continue"))) (some (.fixed 0))
  !(written cmds).contains "Expect" && !(sources cfg s).timers.any (·.1 == .continue)

-- An HTTP/1.0 request is never chunked (RFC 9112 §6.1): a body of unknown length is sent whole,
-- with its `Content-Length`, once it ended.
#guard
  let (s, head) := submit started { request .post with version := .v10 } none
  let (s, first) := pull s "ab"
  let (_, last) := run s (.pulled none)
  written head == "" && written first == "" &&
    written last ==
      "POST / HTTP/1.0\r\nHost: a\r\nUser-Agent: lean-http/1.1\r\nConnection: close\r\nContent-Length: 2\r\n\r\nab"
