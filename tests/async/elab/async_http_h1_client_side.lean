import Std.Http

open Std Http
open Std.Http.Protocol.H1

/-!
Tests the client side of the HTTP/1.1 machine against RFC 9110 and RFC 9112: the request heads it
refuses to write (a target form the method forbids, content with `CONNECT`, a version other than
HTTP/1.0 or HTTP/1.1, a missing or repeated `Host`), and the responses it reads (a long reason
phrase, reframing trailer fields, line breaks before a status line, a response while the request
head is held, an early final response that closes the connection while the body is written).
-/

def request (method : Method) (target : String := "/") (version : Version := .v11)
    (headers : Headers := Headers.empty.insert .host (.mk "a")) : Request.Head :=
  { method, version, uri := RequestTarget.parse! target, headers }

/-- Steps `machine` `n` times, returning it with the output written and the events reported. -/
def run (machine : Machine .sending) (n : Nat := 4) :
    Machine .sending × String × Array (Event .sending) := Id.run do
  let mut machine := machine
  let mut out := ByteArray.empty
  let mut events := #[]
  for _ in [0:n] do
    let (next, res) := machine.step
    machine := next
    out := out ++ res.output.toByteArray
    events := events ++ res.events
  return (machine, String.fromUTF8! out, events)

def fresh : Machine .sending := { config := {} }

/-- A client machine that has written a GET without a body. -/
def sentGet : Machine .sending :=
  (run (fresh.send (request .get) |>.userClosedBody)).1

def endHeaders (events : Array (Event .sending)) : Array Response.Head :=
  events.filterMap fun | .endHeaders head => some head | _ => none

def failedWith (events : Array (Event .sending)) : Array Protocol.H1.Error :=
  events.filterMap fun | .failed err => some err | _ => none

/-- Writes `head` with an empty body, and returns what went on the wire and whether it failed. -/
def write (head : Request.Head) : String × Bool :=
  let (machine, out, _) := run (fresh.send head |>.userClosedBody)
  (out, machine.failed)

/-- Feeds `input` one byte per step. -/
def feedBytewise (machine : Machine .sending) (input : String) :
    Machine .sending × Array (Event .sending) := Id.run do
  let mut machine := machine
  let mut events := #[]
  for b in input.toUTF8 do
    let (next, res) := (machine.feed (ByteArray.mk #[b])).step
    machine := next
    events := events ++ res.events
  return (machine, events)

/-! ## RFC 9112 §3.2.3, §3.2.4: the target form the method allows (W1) -/

#guard (write (request .get "*")).2 && (write (request .get "*")).1.isEmpty
#guard !(write (request .options "*")).2 &&
  (write (request .options "*")).1.startsWith "OPTIONS * HTTP/1.1\r\n"

#guard (write (request .get "a:443")).2 && (write (request .get "a:443")).1.isEmpty
#guard (write (request .connect "/x?y=1")).2
#guard (write (request .connect "http://a/x")).2
#guard (write (request .connect "*")).2
#guard !(write (request .connect "a:443")).2

/-! ## RFC 9110 §9.3.6: a `CONNECT` request has no content (W2) -/

-- The head goes out at once, without framing fields, although the body was not closed.
#guard
  let (machine, out, _) := run (fresh.send (request .connect "a:443"))
  !machine.failed && out == "CONNECT a:443 HTTP/1.1\r\nHost: a\r\n\r\n"

-- Content handed over for it is never written.
#guard
  let (machine, out, _) := run (fresh.send (request .connect "a:443")
    |>.sendData #[Chunk.ofByteArray "hello".toUTF8] |>.userClosedBody)
  machine.failed && out.startsWith "CONNECT a:443 HTTP/1.1\r\n" && (out.splitOn "hello").length == 1

-- A length for it, from its head or from the caller, is refused before anything is written.
#guard (write (request .connect "a:443" (headers := Headers.empty.insert .host (.mk "a")
  |>.insert .contentLength (.mk "5")))).2
#guard
  let (machine, out, _) := run (fresh.sendRequest (request .connect "a:443") (some (.fixed 5))
    |>.sendData #[Chunk.ofByteArray "hello".toUTF8] |>.userClosedBody)
  machine.failed && (out.splitOn "hello").length == 1

/-! ## RFC 9110 §6.2: a request on an HTTP/1.1 connection is HTTP/1.0 or HTTP/1.1 (B3) -/

#guard (write (request .get (version := .v20))).2 && (write (request .get (version := .v20))).1.isEmpty
#guard !(write (request .get (version := .v10))).2

/-! ## RFC 9112 §3.2: one `Host` in an HTTP/1.1 request (W3) -/

#guard (write (request .get (headers := .empty))).2 && (write (request .get (headers := .empty))).1.isEmpty
#guard (write (request .get (headers := Headers.empty.insert .host (.mk "a")
  |>.insert .host (.mk "b")))).2
-- HTTP/1.0 defines no `Host`, so a request without one is written.
#guard !(write (request .get (version := .v10) (headers := .empty))).2

/-! ## RFC 9112 §4: a client ignores the reason phrase (R1) -/

def longReason : String :=
  "HTTP/1.1 200 " ++ String.ofList (List.replicate 600 'R') ++ "\r\nContent-Length: 1\r\n\r\na"

#guard
  let (machine, _, events) := run (sentGet.feed longReason.toUTF8)
  let (machine, chunk?) := machine.pullBody
  !machine.failed && (endHeaders events).map (·.status) == #[.ok] &&
    chunk?.map (·.chunk.data) == some "a".toUTF8

-- The same when the line arrives one byte at a time.
#guard
  let (machine, events) := feedBytewise sentGet longReason
  !machine.failed && (endHeaders events).map (·.status) == #[.ok]

-- The whole status line stays bounded by `maxStartLineLength`.
#guard
  let line := "HTTP/1.1 200 " ++ String.ofList (List.replicate 9000 'R') ++ "\r\n\r\n"
  (run (sentGet.feed line.toUTF8)).1.failed

/-! ## RFC 9110 §6.5.1: a client discards trailer fields, so reframing ones do not fail (R3) -/

#guard ["Content-Length: 1", "Transfer-Encoding: chunked", "Host: b", "Connection: close"].all
  fun trailer =>
    let raw := "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n2\r\nhi\r\n0\r\n" ++ trailer ++
      "\r\n\r\n"
    let (machine, _, _) := run (sentGet.feed raw.toUTF8)
    let machine := machine.drainBody
    !machine.failed && machine.bodyBytesRead > 0 &&
      (machine.isReaderComplete || machine.reader.state matches .pending)

/-! ## RFC 9112 §2.2: line breaks before a status line, whenever they arrive (N1) -/

-- Before the response to the request just sent.
#guard
  let (machine, _, events) := run (sentGet.feed "\r\n\r\nHTTP/1.1 204 No Content\r\n\r\n".toUTF8)
  !machine.failed && (endHeaders events).map (·.status) == #[.noContent]

-- Between two responses, whether they arrive before or after the second request is sent.
#guard
  let (m, _, _) := run (sentGet.feed "HTTP/1.1 204 No Content\r\n\r\n\r\n".toUTF8)
  let (m, _, _) := run (m.send (request .get) |>.userClosedBody)
  let (m, _, events) := run (m.feed "\r\nHTTP/1.1 204 No Content\r\n\r\n".toUTF8)
  !m.failed && (endHeaders events).map (·.status) == #[.noContent]

#guard
  let (m, _, _) := run (sentGet.feed "HTTP/1.1 204 No Content\r\n\r\n".toUTF8)
  let (m, _, _) := run (m.send (request .get) |>.userClosedBody)
  let (m, _, events) := run (m.feed "\r\n\r\nHTTP/1.1 204 No Content\r\n\r\n".toUTF8)
  !m.failed && (endHeaders events).map (·.status) == #[.noContent]

/-! ## RFC 9112 §9.2: no response before the request head is written (C5) -/

-- The head waits for its body's framing; a response then answers no request this client wrote.
#guard
  let held := (run (fresh.send (request .post))).1
  let (machine, out, events) := run (held.feed "HTTP/1.1 200 OK\r\nContent-Length: 0\r\n\r\n".toUTF8)
  let (machine, out', _) := run (machine.sendData #[Chunk.ofByteArray "ab".toUTF8] |>.userClosedBody)
  machine.failed && failedWith events == #[.badMessage] && (endHeaders events).isEmpty &&
    out.isEmpty && out'.isEmpty

-- EOF while the head is held ends the exchange at once.
#guard
  let held := (run (fresh.send (request .post))).1
  let (machine, _, events) := run held.noMoreInput
  machine.failed && failedWith events == #[.connectionClosed]

-- Line breaks alone are still discarded.
#guard
  let held := (run (fresh.send (request .post))).1
  let (machine, _, _) := run (held.feed "\r\n".toUTF8)
  !machine.failed

/-! ## RFC 9112 §9.5: stop writing the body once the server answers and closes (C3) -/

def postFour : Request.Head :=
  request .post (headers := Headers.empty.insert .host (.mk "a") |>.insert .contentLength (.mk "4"))

#guard
  let (m, out, _) := run (fresh.send postFour |>.sendData #[Chunk.ofByteArray "ab".toUTF8])
  let (m, _, _) := run (m.feed
    "HTTP/1.1 413 Content Too Large\r\nConnection: close\r\nContent-Length: 0\r\n\r\n".toUTF8)
  let (m, out', _) := run (m.sendData #[Chunk.ofByteArray "cd".toUTF8] |>.userClosedBody)
  !m.failed && out.endsWith "\r\n\r\nab" && out'.isEmpty && m.writer.state matches .closed

-- With keep-alive the server reads the rest, so the body is still written.
#guard
  let (m, _, _) := run (fresh.send postFour |>.sendData #[Chunk.ofByteArray "ab".toUTF8])
  let (m, _, _) := run (m.feed "HTTP/1.1 200 OK\r\nContent-Length: 0\r\n\r\n".toUTF8)
  let (m, out', _) := run (m.sendData #[Chunk.ofByteArray "cd".toUTF8] |>.userClosedBody)
  !m.failed && out' == "cd"
