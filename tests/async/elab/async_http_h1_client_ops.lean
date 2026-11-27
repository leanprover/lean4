import Std.Http

open Std Http
open Std.Http.Protocol.H1

/-!
Tests the HTTP/1.1 machine operations a client connection uses: `hasBufferedInput`,
`bufferedInputBytes`, `bodyBytesRead`, `needsInput`, `exhausted`, `hasPendingEvents`, `shutdown`,
`sendRequest`, `awaitsContinue`, `isWritingBody`, `isReadingBody`, `outgoingBodySupplied`,
`peerWillNotReadBody`, `abandonOutgoingBody`, `drainBody`, and the public
`Message.Head.hasExpectContinue`; also the `WWW-Authenticate` and `Proxy-Authenticate` names.
-/

def request (method : Method) (headers : Headers := .empty) : Request.Head :=
  { method, version := .v11, uri := RequestTarget.parse! "/",
    headers := headers.insert .host (.mk "a") }

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

/-- A client machine that has written nothing. -/
def fresh : Machine .sending := { config := {} }

/-- A client machine that has written a GET without a body. -/
def sentGet (config : Protocol.H1.Config := {}) : Machine .sending :=
  (run (({ config } : Machine .sending).send (request .get) |>.userClosedBody)).1

def response (head : String) (body : String := "") : ByteArray :=
  (head ++ "\r\n" ++ body).toUTF8

/-! ## `hasBufferedInput` -/

-- Fed but not parsed: buffered. Once stepped through the whole response: nothing left.
#guard
  let fed := sentGet.feed (response "HTTP/1.1 204 No Content\r\n")
  fed.hasBufferedInput && !(run fed).1.hasBufferedInput

#guard !sentGet.hasBufferedInput

/-! ## `bodyBytesRead` -/

-- Counts the body bytes pulled for the current message.
#guard
  let (m, _, _) := run (sentGet.feed (response "HTTP/1.1 200 OK\r\nContent-Length: 5\r\n" "hello"))
  let (m, chunk?) := m.pullBody
  chunk?.map (·.chunk.data.size) == some 5 && m.bodyBytesRead == 5

-- `drainBody` counts as well, so a body nobody reads gives the same total.
#guard
  let (m, _, _) := run (sentGet.feed (response "HTTP/1.1 200 OK\r\nContent-Length: 10\r\n" "0123456789"))
  m.drainBody.bodyBytesRead == 10

/-! ## `needsInput` and `exhausted` -/

#guard sentGet.needsInput && !sentGet.exhausted

-- The peer closing its side ends the input; with no body left to hand out, nothing is left to do.
#guard
  let m := sentGet.noMoreInput
  !m.needsInput && m.exhausted

-- A response fed together with EOF but not yet stepped is work left: the next `step` reads it.
#guard
  let m := (sentGet.feed (response "HTTP/1.1 200 OK\r\nContent-Length: 2\r\n" "hi")).noMoreInput
  !m.exhausted && (run m 1).1.canPullBodyNow

-- Bytes left after the reader closed are never read, so they do not keep the machine going.
#guard
  let m := (sentGet.feed (response "HTTP/1.1 200 OK\r\nConnection: close\r\nContent-Length: 0\r\n" "xyz")).noMoreInput
  let (m, _, _) := run m
  m.isReaderClosed && m.exhausted

-- A buffered body still to pull keeps the machine from being exhausted after EOF.
#guard
  let (m, _, _) := run (sentGet.feed (response "HTTP/1.1 200 OK\r\nContent-Length: 5\r\n" "hello"))
  let m := m.noMoreInput
  !m.needsInput && m.canPullBodyNow && !m.exhausted

/-! ## `hasPendingEvents` -/

-- Input past the buffer bound fails the machine in `feed`, outside `step`; `step` then reports it.
#guard
  let config : Protocol.H1.Config :=
    { maxBufferedBodyBytes := some 0, maxHeaderBytes := 0, maxStartLineLength := 0, maxChunkLineLength := 0 }
  let m := (sentGet config).feed (response "HTTP/1.1 204 No Content\r\n")
  let (stepped, _, events) := run m 1
  !sentGet.hasPendingEvents && m.hasPendingEvents && !stepped.hasPendingEvents &&
    events.any (· matches .failed .entityTooLarge)

/-! ## `shutdown` -/

-- A request not written yet stays unwritten, and the machine takes no more input.
#guard
  let m := fresh.send (request .get) |>.userClosedBody |>.shutdown
  let (m, out, _) := run m
  out.isEmpty && !m.needsInput

-- `shutdown` stops reading without claiming the peer closed its side.
#guard
  let m := sentGet.shutdown
  !m.reader.peerClosed && m.reader.inputStopped

/-! ## `sendRequest` -/

-- A known size goes out as `Content-Length`.
#guard
  let m := fresh.sendRequest (request .post) (some (.fixed 3))
    |>.sendData #[Chunk.ofByteArray "abc".toUTF8] |>.userClosedBody
  let (_, out, _) := run m
  (out.splitOn "Content-Length: 3\r\n").length == 2 && out.endsWith "\r\n\r\nabc"

-- No known size and `Expect: 100-continue`: the body is chunked, since the head goes out first.
#guard
  let headers := Headers.empty.insert .expect (.mk "100-continue")
  let m := fresh.sendRequest (request .post headers) none
  m.writer.knownSize == some .chunked

-- No known size and no expectation: the length is left to the head and the body.
#guard
  let m := fresh.sendRequest (request .post) none
  m.writer.knownSize.isNone

-- The head's own `Content-Length` wins over the expectation's chunked default.
#guard
  let headers := Headers.empty.insert .expect (.mk "100-continue") |>.insert .contentLength (.mk "4")
  let m := fresh.setKnownSize (.fixed 4) |>.sendRequest (request .post headers) none
  m.writer.knownSize == some (.fixed 4)

/-! ## `awaitsContinue` and `Message.Head.hasExpectContinue` -/

#guard
  let headers := Headers.empty.insert .expect (.mk "100-continue")
  (fresh.sendRequest (request .post headers) none).awaitsContinue

#guard !(fresh.sendRequest (request .post) none).awaitsContinue

-- The expectation is a list member compared case-insensitively; a member with a value is another one.
#guard Message.Head.hasExpectContinue (dir := .receiving)
  (request .post (Headers.empty.insert .expect (.mk "foo, 100-Continue")))
#guard !Message.Head.hasExpectContinue (dir := .receiving)
  (request .post (Headers.empty.insert .expect (.mk "100-continue=x")))

-- HTTP/1.0 defines no 1xx status, so the expectation never applies.
#guard !Message.Head.hasExpectContinue (dir := .receiving)
  { request .post (Headers.empty.insert .expect (.mk "100-continue")) with version := .v10 }

/-! ## `isWritingBody`, `peerWillNotReadBody` and `abandonOutgoingBody` -/

/-- A POST announcing 10 body bytes with 3 written, answered with `answer` before the rest. -/
def partlySentPost (answer : String) : Machine .sending :=
  let m := fresh.send
      (request .post (Headers.empty.insert .contentLength (.mk "10")))
    |>.setKnownSize (.fixed 10) |>.sendData #[Chunk.ofByteArray "abc".toUTF8]
  let (m, _, _) := run m
  (run (m.feed (response answer))).1

-- A `close` answer whose body is still arriving: the server will not read the remaining 7 bytes,
-- so abandon them. Once such an answer is complete, the machine abandons them itself.
#guard
  let m := partlySentPost "HTTP/1.1 413 Content Too Large\r\nConnection: close\r\nContent-Length: 5\r\n"
  m.isWritingBody && m.peerWillNotReadBody

#guard
  let m := partlySentPost "HTTP/1.1 413 Content Too Large\r\nConnection: close\r\nContent-Length: 5\r\n"
  let (m, out, _) := run m.abandonOutgoingBody
  !m.isWritingBody && !m.keepAlive && out.isEmpty

-- A keep-alive answer: the server may still read the body, so this is not reported.
#guard
  let m := partlySentPost "HTTP/1.1 413 Content Too Large\r\nContent-Length: 0\r\n"
  m.isWritingBody && m.keepAlive && !m.peerWillNotReadBody

-- Abandoning anyway turns keep-alive off: the 7 announced bytes are still owed, so the next request
-- would be read as their rest.
#guard
  let m := partlySentPost "HTTP/1.1 413 Content Too Large\r\nContent-Length: 0\r\n"
  !m.abandonOutgoingBody.keepAlive

-- Data queued but not written is dropped.
#guard
  let m := partlySentPost "HTTP/1.1 413 Content Too Large\r\nContent-Length: 0\r\n"
  let m := m.sendData #[Chunk.ofByteArray "defg".toUTF8] |>.abandonOutgoingBody
  let (_, out, _) := run m
  out.isEmpty

-- A body whose announced bytes are all written truncates nothing, so keep-alive stays.
#guard
  let m := fresh.send
      (request .post (Headers.empty.insert .contentLength (.mk "3")))
    |>.setKnownSize (.fixed 3) |>.sendData #[Chunk.ofByteArray "abc".toUTF8] |>.userClosedBody
  let (m, _, _) := run m
  !m.isWritingBody && m.abandonOutgoingBody.keepAlive

-- Bytes queued but not yet written are still owed: abandoning them turns keep-alive off.
#guard
  let m := fresh.send
      (request .post (Headers.empty.insert .contentLength (.mk "3")))
    |>.setKnownSize (.fixed 3) |>.sendData #[Chunk.ofByteArray "abc".toUTF8]
  let (m, _, _) := run m
  m.isWritingBody && !m.abandonOutgoingBody.keepAlive

/-! ## `drainBody` -/

-- Draining frees the reader for the next response on the connection.
#guard
  let (m, _, _) := run (sentGet.feed (response "HTTP/1.1 200 OK\r\nContent-Length: 10\r\n" "0123456789"))
  let m := m.drainBody
  !m.canPullBodyNow &&
    let (m, _, _) := run m
    let (m, _, _) := run ((m.send (request .get)).userClosedBody)
    let (_, _, events) := run (m.feed (response "HTTP/1.1 204 No Content\r\n"))
    events.any (· matches .endHeaders _)

/-! ## `bufferedInputBytes` -/

-- Counts the input not parsed yet: all of it before a step, none once the response is read.
#guard
  let raw := response "HTTP/1.1 204 No Content\r\n"
  let fed := sentGet.feed raw
  fed.bufferedInputBytes == raw.size && (run fed).1.bufferedInputBytes == 0

-- A body nobody pulls stays buffered.
#guard
  let (m, _, _) := run (sentGet.feed (response "HTTP/1.1 200 OK\r\nContent-Length: 5\r\n" "hello"))
  m.bufferedInputBytes == 5

/-! ## `isReadingBody` -/

-- In the body until its last byte is pulled.
#guard
  let (m, _, _) := run (sentGet.feed (response "HTTP/1.1 200 OK\r\nContent-Length: 5\r\n" "hello"))
  m.isReadingBody && !m.drainBody.isReadingBody

-- Not before the head is read, nor for a response without a body.
#guard !sentGet.isReadingBody
#guard !(run (sentGet.feed (response "HTTP/1.1 204 No Content\r\n"))).1.isReadingBody

/-! ## `outgoingBodySupplied` -/

-- A fixed-length body with all its bytes handed over: the last ones wait for the caller to close it.
#guard
  let m := fresh.send (request .post (Headers.empty.insert .contentLength (.mk "3")))
    |>.setKnownSize (.fixed 3) |>.sendData #[Chunk.ofByteArray "abc".toUTF8]
  (run m).1.outgoingBodySupplied

-- Bytes still owed, or a chunked body the caller has not closed: more is needed.
#guard
  let m := fresh.send (request .post (Headers.empty.insert .contentLength (.mk "3")))
    |>.setKnownSize (.fixed 3) |>.sendData #[Chunk.ofByteArray "ab".toUTF8]
  !(run m).1.outgoingBodySupplied

#guard
  let m := fresh.send (request .post) |>.sendData #[Chunk.ofByteArray "ab".toUTF8]
  !(run m).1.outgoingBodySupplied

-- A request written whole, and a fixed-length body written and closed.
#guard (run (fresh.send (request .get) |>.userClosedBody)).1.outgoingBodySupplied
#guard
  let m := fresh.send (request .post (Headers.empty.insert .contentLength (.mk "3")))
    |>.setKnownSize (.fixed 3) |>.sendData #[Chunk.ofByteArray "abc".toUTF8] |>.userClosedBody
  (run m).1.outgoingBodySupplied

/-! ## Authentication header names -/

#guard Header.Name.wwwAuthenticate == Header.Name.ofString! "WWW-Authenticate"
#guard Header.Name.proxyAuthenticate == Header.Name.ofString! "Proxy-Authenticate"
