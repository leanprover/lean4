module

import Std.Http.Test.Helpers
import Std.Http.Test.Machine

/-!
# HTTP/1.1 client framing

`Machine .sending`: how a client reads the status line, fields, bodies, trailers and interim responses
of a response, and how it writes request heads and request bodies. RFC 9110 §2.5, §5.5, §6.5,
§8.6, §15.2; RFC 9112 §4, §6, §7.1. Regressions: #16282.
-/

open Std Http
open Std.Async
open Std.Http.Internal
open Std.Http.Protocol.H1
open Std.Http.Internal.Test

private def mkGet10 (path : String := "/") : String :=
  s!"GET {path} HTTP/1.0\r\n\r\n"

private def mkPostHead (path : String) (bodyLen : Nat) (extra : String := "") : String :=
  rawRequest "POST" path (extra := s!"Content-Length: {bodyLen}\r\n{extra}")

private def minimalGetRequest : Request.Head :=
  { method := .get, version := .v11, uri := RequestTarget.originForm! "/",
    headers := Headers.empty.insert! "Host" "example.com" }

private def run (machine : Machine dir) (n : Nat := 4) : Machine dir × String := Id.run do
  let mut machine := machine
  let mut out := ByteArray.empty
  for _ in [0:n] do
    let (next, step) := machine.step
    machine := next
    out := out ++ step.output.toByteArray
  return (machine, String.fromUTF8! out)

private def expect (cond : Bool) (msg : String) : IO Unit :=
  unless cond do throw (IO.userError msg)

private def post (version : Version) : Request.Head :=
  { method := .post, version, uri := RequestTarget.parse! "/",
    headers := Headers.empty.insert Header.Name.host (.mk "a") }

/-- Sends a POST whose body arrives in a later step than its head, and returns the wire bytes. -/
private def sendLateBody (version : Version) : Machine .sending × String :=
  let m : Machine .sending := { config := {} }
  let (m, first) := run (m.send (post version) |>.sendData #[Chunk.ofByteArray "hello".toUTF8]) 2
  let (m, rest) := run m.userClosedBody 3
  (m, first ++ rest)

/-- A request head that declares a 10-byte body. -/
private def putHead : Request.Head :=
  (Request.new |>.method .put |>.uri! "/upload" |>.header! "Host" "example.com"
    |>.header! "Content-Length" "10").line

/-- Steps `machine` until a step writes `needle`, and reports whether that step also closed. -/
private def closesWhenWriting (machine : Machine dir) (needle : String) : IO Bool := do
  let mut machine := machine
  for _ in [0:8] do
    let (next, step) := machine.step
    machine := next
    let wrote := String.fromUTF8! (step.output.data.foldl (· ++ ·) .empty)
    if wrote.contains needle then
      return step.events.any (· matches .close) && machine.error == some .badMessage
  throw <| IO.userError s!"{needle.quote} was never written"

private def getHead (method : Method) : Request.Head :=
  { method, version := .v11, uri := RequestTarget.parse! "/", headers := Headers.empty.insert .host (.mk "a") }

/-- Sends a GET, reads `first` and `early`, then sends a HEAD; returns the bytes written for it. -/
private def secondRequest (early : ByteArray) : ByteArray := Id.run do
  let mut m : Machine .sending := { config := {} }
  m := m.send (getHead .get) |>.userClosedBody
  let (m1, _) := m.step
  m := m1.feed ("HTTP/1.1 204 No Content\r\n\r\n".toUTF8 ++ early)
  for _ in [0:4] do
    m := m.step.1
  m := m.send (getHead .head) |>.userClosedBody
  let mut out := ByteArray.empty
  for _ in [0:4] do
    let (m', res) := m.step
    m := m'
    out := out ++ res.output.toByteArray
  return out

/-- A server machine that has read `request`. -/
private def server (request : String) : Machine .receiving :=
  (({ config := {} } : Machine .receiving).feed request.toUTF8).step.1

private def headers (fields : List (Header.Name × String)) : Headers :=
  fields.foldl (fun hs (name, value) => hs.insert name (Header.Value.ofString! value)) .empty

private def get : String := "GET / HTTP/1.1\r\nHost: a\r\n\r\n"

private def abc : Array Chunk := #[Chunk.ofByteArray "abc".toUTF8]

/-! ## Status line and fields (RFC 9112 §4, RFC 9110 §2.5, §5.5) -/

#eval checkCases "Status line and fields: machine" #[
    ("§5.5: obs-text in a response field value is accepted", do
      -- §5.5: a recipient treats obs-text in a field value as opaque data
      MachineTester.sending "§5.5: obs-text in a response field value is accepted"
        |>.send minimalGetRequest |>.step
        |>.feedBytes ("HTTP/1.1 200 OK\r\nContent-Disposition: attachment; filename=\"caf".toUTF8
          ++ ByteArray.mk #[0xC3, 0xA9] ++ ".txt\"\r\nX-Latin1: caf".toUTF8 ++ ByteArray.mk #[0xE9]
          ++ "\r\nContent-Length: 0\r\n\r\n".toUTF8)
        |>.step |>.assertNoError |>.assertHasEndHeaders
        |>.onEndHeaders (fun t head =>
          let disposition := (head.headers.get? (.ofString! "Content-Disposition")).map (·.value)
          let latin1 := (head.headers.get? (.ofString! "X-Latin1")).map (·.value)
          if disposition != some "attachment; filename=\"café.txt\"" then
            t.addError s!"Content-Disposition mismatch: {repr disposition}"
          else if latin1 != some "caf\uFFFD" then
            t.addError s!"X-Latin1 mismatch: {repr latin1}"
          else t)
        |>.run),
    ("§4: obs-text in the reason phrase is accepted", do
      -- §4: obs-text in a reason phrase, which a client ignores
      MachineTester.sending "§4: obs-text in the reason phrase is accepted"
        |>.send minimalGetRequest |>.step
        |>.feedBytes ("HTTP/1.1 200 Tr".toUTF8 ++ ByteArray.mk #[0xC3, 0xA8] ++ "s bien ".toUTF8
          ++ ByteArray.mk #[0xFF] ++ "\r\nContent-Length: 0\r\n\r\n".toUTF8)
        |>.step |>.assertNoError
        |>.onEndHeaders (fun t head =>
          if head.status.toCode != 200 then t.addError s!"expected 200, got {head.status.toCode}" else t)
        |>.run),
    ("§4: status line with no space after the code is accepted", do
      -- §4: a status line that ends right after the status code
      MachineTester.sending "§4: status line with no space after the code is accepted"
        |>.send minimalGetRequest |>.step
        |>.feed "HTTP/1.1 204\r\n\r\n"
        |>.step |>.assertNoError
        |>.onEndHeaders (fun t head =>
          if head.status != .noContent then t.addError s!"expected 204, got {head.status.toCode}" else t)
        |>.run),
    ("§2.5: HTTP/1.2 response is read as HTTP/1.1", do
      -- §2.5: a higher minor version is processed as the highest minor version the recipient implements
      MachineTester.sending "§2.5: HTTP/1.2 response is read as HTTP/1.1"
        |>.send minimalGetRequest |>.step
        |>.feed "HTTP/1.2 200 OK\r\nContent-Length: 2\r\n\r\nok"
        |>.step |>.assertNoError |>.assertKeepAlive
        |>.onEndHeaders (fun t head =>
          if head.version != .v11 then t.addError s!"expected HTTP/1.1, got {repr head.version}" else t)
        |>.drainBody |>.assertPulledBody "ok".toUTF8 |>.run)
  ] (·.2)

#eval checkCases "Status line and fields: async_http_response_framing.lean" #[
    ("RFC 9112 §4, §6.3: parse a 200 response with headers",
      do
        -- Parse a 200 response with headers
        let machineA : Protocol.H1.Machine .sending := { config := {}, reader := { state := .needStartLine } }
        let rawA := "HTTP/1.1 200 OK\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\n\x0d\n"
        let (machineA', stepA) := (machineA.feed rawA.toUTF8).step
        if stepA.events.any (fun | .failed _ => true | _ => false) then
          throw <| IO.userError s!"unexpected failure parsing 200 response: {repr stepA.events}"
        unless stepA.events.any (fun | .endHeaders _ => true | _ => false) do
          throw <| IO.userError s!"missing endHeaders event: {repr stepA.events}"
        unless machineA'.reader.messageHead.status == .ok do
          throw <| IO.userError s!"unexpected status: {repr machineA'.reader.messageHead.status}"
        unless machineA'.reader.messageHead.headers.hasEntry Header.Name.contentLength (Header.Value.ofString! "0") do
          throw <| IO.userError "missing Content-Length header in parsed response")
  ] (·.2)


/-- A client that sent `request` and then read `raw` in one read. -/
private def clientRead (raw : ByteArray) (request : Request.Head := minimalGetRequest) : MachineTester .sending :=
  MachineTester.sending "client" |>.send request |>.step |>.feedBytes raw |>.step

/-- A failure leaves `error` set; the reader may already have moved on from `.failed`. -/
private def hasFailed (m : Machine .sending) : Bool := m.failed || m.error.isSome

private def expectFailed (raw : ByteArray) (request : Request.Head := minimalGetRequest) : IO Unit := do
  let t := clientRead raw request
  ensure (hasFailed t.machine) s!"expected a failure for {(String.fromUTF8? raw).getD "<bytes>" |>.quote}, got {repr (t.lastStep.map (·.events))}"

private def expectStatus (raw : ByteArray) (check : Status → Bool) (what : String) : IO Unit :=
  clientRead raw |>.assertNoError |>.assertHasEndHeaders
    |>.onEndHeaders (fun t head => if check head.status then t else t.addError s!"{what}: got {head.status.toCode}") |>.run

-- RFC 9112 §4: `status-code = 3DIGIT`, then SP.
#eval checkCases "Status lines that fail" #[
    "HTTP/1.1 20X OK", "HTTP/1.1 abcd", "HTTP/1.1  Unknown", "HTTP/1.1 c8 OK", "HTTP/1.1 0x12d OK",
    "HTTP/1.1 20 OK", "HTTP/1.1 1000 OK", "HTTP/1.1 -10 OK", "HTTP/1.1 400.100 Not Ok", "HTTP/1.1 99 200 OK",
    "HTTP/1.1   200  OK", "HTTP/1.0  401 Unauthorized", "HTTP/1.1 200\x0dOK"
  ] fun line => expectFailed s!"{line}\r\nContent-Length: 0\r\n\r\n".toUTF8

-- RFC 9110 §15: a client treats a status code outside 100–599 as a 5xx.
#eval checkCases "Status codes that are accepted" #[
    ("200 OK", "200 OK", fun (s : Status) => s.toCode == 200), ("404 NOTFOUND", "404 NOTFOUND", (·.toCode == 404)),
    ("999 Done", "999 Done", (·.isServerError)),
    ("600–999", "", (·.isServerError)),
    ("000", "000 X", (·.isServerError)), ("001", "001 X", (·.isServerError)), ("099", "099 X", (·.isServerError))
  ] fun (label, rest, check) => do
    if label == "600–999" then
      for code in [600:1000] do
        expectStatus s!"HTTP/1.1 {code} X\r\nContent-Length: 0\r\n\r\n".toUTF8 check s!"{code}"
    else
      expectStatus s!"HTTP/1.1 {rest}\r\nContent-Length: 0\r\n\r\n".toUTF8 check label

#eval checkCases "Reason phrases" #[
    ("HTTP/1.0 303 SP, then CRLF", "HTTP/1.0 303 \r\nContent-Length: 0\r\n\r\n".toUTF8, true),
    ("no reason, then a field", "HTTP/1.1 200\r\nFoo: bar\r\nContent-Length: 0\r\n\r\n".toUTF8, true),
    ("a reason ending in HTAB", "HTTP/1.1 200 OK\t\r\nContent-Length: 0\r\n\r\n".toUTF8, true),
    ("obs-text", "HTTP/1.1 200 X".toUTF8 ++ ByteArray.mk #[0xFF] ++ "Z\r\nContent-Length: 0\r\n\r\n".toUTF8, true),
    ("NUL", "HTTP/1.1 200 O\x00K\r\nContent-Length: 0\r\n\r\n".toUTF8, false)
  ] fun (_, raw, ok) => if ok then (clientRead raw |>.assertNoError |>.assertHasEndHeaders |>.run) else expectFailed raw

#eval checkCases "Status-line versions" #[
    ("HTTP/2.0 is unsupported", clientRead "HTTP/2.0 200 OK\r\nContent-Length: 0\r\n\r\n".toUTF8
      |>.assertFailedWith .unsupportedVersion |>.run),
    ("HTTP/1.100000000002", expectFailed "HTTP/1.100000000002 200 OK\r\nContent-Length: 0\r\n\r\n".toUTF8),
    ("HTTP/1.-1", expectFailed "HTTP/1.-1 200 OK\r\nContent-Length: 0\r\n\r\n".toUTF8),
    ("HTTP/A.B", expectFailed "HTTP/A.B 200 OK\r\nContent-Length: 0\r\n\r\n".toUTF8),
    ("HTTP/1", expectFailed "HTTP/1 200 OK\r\nContent-Length: 0\r\n\r\n".toUTF8),
    ("http/1.1", expectFailed "http/1.1 200 OK\r\nContent-Length: 0\r\n\r\n".toUTF8)
  ] (·.2)

-- RFC 9112 §4: a response starts with `HTTP-name`; other first bytes fail without waiting for a line.
#eval checkCases "Non-HTTP first bytes" #[
    ("NUL", ByteArray.mk #[0x00]), ("SP", " ".toUTF8),
    ("a TLS ServerHello", ByteArray.mk #[0x16, 0x03, 0x03, 0x00, 0x31]), ("CRLF", "\r\n".toUTF8)
  ] fun (_, raw) => expectFailed raw

#eval checkCases "Response field syntax that fails" #[
    ("a SP line before the first field", "HTTP/1.1 200 OK\r\n Foo: bar\r\nContent-Length: 0\r\n\r\n"),
    ("a HTAB line before the first field", "HTTP/1.1 200 OK\r\n\tFoo: bar\r\nContent-Length: 0\r\n\r\n"),
    (": nval", "HTTP/1.1 200 OK\r\n: nval\r\nContent-Length: 0\r\n\r\n"),
    ("a line without a colon", "HTTP/1.1 200 OK\r\nFoo\r\nContent-Length: 0\r\n\r\n")
  ] fun (_, raw) => expectFailed raw.toUTF8

private def foldedValue (raw : String) : Option String := Id.run do
  let t := clientRead raw.toUTF8
  let some step := t.lastStep | return none
  for e in step.events do
    if let .endHeaders head := e then
      return (head.headers.get? (.ofString! "X-Fold")).map (·.value)
  return none

-- RFC 9112 §5.2: a user agent MUST replace each obs-fold with one or more SP before interpreting the value.
#eval checkCases "obs-fold in a response is unfolded" #[
    ("in the middle", "X-Fold: text\r\n folded with space\r\n\tfolded with tab", "text folded with space folded with tab"),
    ("at the start", "X-Fold:\r\n text", "text"), ("at the end", "X-Fold: text\r\n ", "text"),
    ("the whole value", "X-Fold:\r\n ", "")
  ] fun (_, field, want) => do
    let got := foldedValue s!"HTTP/1.1 200 OK\r\n{field}\r\nContent-Length: 0\r\n\r\n"
    ensure (got == some want) s!"expected {want.quote}, got {repr got}"

-- RFC 9110 §5.3: `Set-Cookie` lines are never combined.
#eval checkCases "Two Set-Cookie lines" #[
    ("two values, in order", clientRead "HTTP/1.1 200 OK\r\nSet-Cookie: a=1; Path=/\r\nSet-Cookie: b=2\r\nContent-Length: 0\r\n\r\n".toUTF8
      |>.assertNoError
      |>.onEndHeaders (fun t head =>
        let vs := (head.headers.getAll? (.ofString! "Set-Cookie")).map (·.map (·.value))
        if vs == some #["a=1; Path=/", "b=2"] then t else t.addError s!"got {repr vs}")
      |>.run)
  ] (·.2)

/-! ## Response body framing (RFC 9112 §6.3, §7.1) -/

#eval checkCases "Response body framing: machine" #[
    ("§6.3: response Content-Length body delivered exactly", do
      let respBody := "Hello!".toUTF8
      MachineTester.sending "§6.3: response Content-Length body delivered exactly"
        |>.send minimalGetRequest |>.step
        |>.feed s!"HTTP/1.1 200 OK\r\nContent-Length: {respBody.size}\r\n\r\n"
        |>.feedBytes respBody |>.step |>.assertNoError
        |>.drainBody |>.assertPulledBody respBody |>.assertLastChunkFinal |>.run),
    ("§6.3: EOF-delimited response body; keep-alive disabled", do
      let eofBody := "eof body".toUTF8
      MachineTester.sending "§6.3: EOF-delimited response body; keep-alive disabled"
        |>.send minimalGetRequest |>.step
        |>.feed "HTTP/1.1 200 OK\r\n\r\n"
        |>.step |>.assertNoError |>.assertNotKeepAlive
        |>.feedBytes eofBody |>.noMoreInput
        |>.drainBody |>.assertPulledBody eofBody |>.assertLastChunkFinal |>.run),
    ("§7.1: response chunked body decoded", do
      -- §7.1: 200 response with chunked body decoded correctly
      let respBody := "chunked".toUTF8
      MachineTester.sending "§7.1: response chunked body decoded"
        |>.send minimalGetRequest |>.step
        |>.feed "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n7\r\nchunked\r\n0\r\n\r\n"
        |>.step |>.assertNoError
        |>.drainBody |>.assertPulledBody respBody |>.assertLastChunkFinal |>.run),
    ("§6.3: HEAD response with contradictory framing fields completes", do
      -- §6.3 rule 1: a response to HEAD ends at its header block, whatever its framing fields say
      MachineTester.sending "§6.3: HEAD response with contradictory framing fields completes"
        |>.send { minimalGetRequest with method := .head } |>.step
        |>.feed "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\nContent-Length: 10\r\n\r\n"
        |>.step |>.assertNoError |>.assertReaderComplete |>.run),
    ("§6.3: 204 response with contradictory framing fields completes", do
      -- §6.3 rule 1: so does a 204 response
      MachineTester.sending "§6.3: 204 response with contradictory framing fields completes"
        |>.send minimalGetRequest |>.step
        |>.feed "HTTP/1.1 204 No Content\r\nTransfer-Encoding: chunked\r\nContent-Length: 5\r\n\r\n"
        |>.step |>.assertNoError |>.assertReaderComplete |>.run),
    ("§6.3 rule 4: a response whose final transfer coding is not chunked is read until the server closes", do
      -- §6.3 rule 4: a response whose final transfer coding is not chunked is read until the server closes
      for coding in ["gzip", "chunked, gzip", "gzip;level=1", "gzip ; level = \"9\""] do
        MachineTester.sending s!"§6.3: Transfer-Encoding: {coding} response is close-delimited"
          |>.send minimalGetRequest |>.step
          |>.feed s!"HTTP/1.1 200 OK\r\nTransfer-Encoding: {coding}\r\n\r\nabc"
          |>.step |>.assertNoError |>.assertNotKeepAlive
          |>.noMoreInput |>.drainBody |>.assertNoError
          |>.assertPulledBody "abc".toUTF8 |>.assertLastChunkFinal |>.run),
    ("§6.3: Transfer-Encoding: gzip;level=1, chunked response is chunked", do
      -- §7: transfer parameters do not change which coding is final
      MachineTester.sending "§6.3: Transfer-Encoding: gzip;level=1, chunked response is chunked"
        |>.send minimalGetRequest |>.step
        |>.feed "HTTP/1.1 200 OK\r\nTransfer-Encoding: gzip;level=1, chunked\r\n\r\n3\r\nabc\r\n0\r\n\r\n"
        |>.step |>.assertNoError |>.assertKeepAlive
        |>.drainBody |>.assertNoError |>.assertPulledBody "abc".toUTF8 |>.assertLastChunkFinal |>.run),
    ("§7.1: chunked defines no parameters", do
      -- §7.1: chunked defines no parameters
      for coding in ["chunked;x=1", "gzip;level, chunked", "gzip;=1, chunked"] do
        MachineTester.sending s!"§7: Transfer-Encoding: {coding} → badMessage"
          |>.send minimalGetRequest |>.step
          |>.feed s!"HTTP/1.1 200 OK\r\nTransfer-Encoding: {coding}\r\n\r\n3\r\nabc\r\n0\r\n\r\n"
          |>.step |>.assertFailedWith .badMessage |>.run),
    ("§8.6: client HEAD response — body suppressed despite Content-Length", do
      -- §8.6: a HEAD response has no body regardless of framing headers. The client reader must treat
      -- it as zero-length and finish without blocking, even though Content-Length advertises bytes that
      -- never arrive on the wire.
      MachineTester.sending "§8.6: client HEAD response — body suppressed despite Content-Length"
        |>.send { minimalGetRequest with method := .head } |>.step
        |>.feed "HTTP/1.1 200 OK\r\nContent-Length: 100\r\n\r\n"
        |>.step
        |>.assertNoError
        |>.assert (fun m => !m.canPullBody)
            "HEAD response must expose no body to pull (reader must not block on absent body bytes)"
        |>.assertReaderComplete |>.run),
    ("§6.3: client zero-length response auto-completes without pullBody", do
      -- §6.3: a client response with a known zero-length body (e.g. 204) must auto-complete; otherwise
      -- the connection would stall waiting for a `pullBody` that never produces bytes.
      MachineTester.sending "§6.3: client zero-length response auto-completes without pullBody"
        |>.send minimalGetRequest |>.step
        |>.feed "HTTP/1.1 204 No Content\r\nContent-Length: 0\r\n\r\n"
        |>.step
        |>.assertNoError
        |>.assert (fun m => !m.canPullBody)
            "zero-length response body must not require a caller pullBody to advance"
        |>.assertReaderComplete |>.run)
  ] (·.2)

#eval checkCases "Response body framing: async_http_response_framing.lean" #[
    ("Parse headerless 204",
      do
        -- Parse headerless 204
        let machineB : Protocol.H1.Machine .sending := { config := {}, reader := { state := .needStartLine } }
        let rawB := "HTTP/1.1 204 No Content\x0d\n\x0d\n"
        let (_, stepB) := (machineB.feed rawB.toUTF8).step
        if stepB.events.any (fun | .failed _ => true | _ => false) then
          throw <| IO.userError s!"unexpected failure parsing 204: {repr stepB.events}"
        if stepB.events.any (fun | .needMoreData _ => true | _ => false) then
          throw <| IO.userError s!"unexpected needMoreData for 204: {repr stepB.events}"
        unless stepB.events.any (fun | .endHeaders _ => true | _ => false) do
          throw <| IO.userError s!"missing endHeaders for 204: {repr stepB.events}"

        -- 204 with Content-Length in response: body framing should be ignored
        let machineC : Protocol.H1.Machine .sending := { config := {}, reader := { state := .needStartLine } }
        let rawC := "HTTP/1.1 204 No Content\x0d\nContent-Length: 5\x0d\n\x0d\nHELLO"
        let (machineC', stepC) := (machineC.feed rawC.toUTF8).step
        if stepC.events.any (fun | .failed _ => true | _ => false) then
          throw <| IO.userError s!"unexpected failure for 204 with framing: {repr stepC.events}"
        -- The 5 bytes of "HELLO" should remain unread
        unless machineC'.reader.input.remainingBytes == 5 do
          throw <| IO.userError s!"expected 5 unread bytes, got {machineC'.reader.input.remainingBytes}")
  ] (·.2)


-- RFC 9112 §6.3 rules 1, 3, 5.
#eval checkCases "Response Content-Length" #[
    ("two lines that differ", expectFailed "HTTP/1.1 200 OK\r\nContent-Length: 3\r\nContent-Length: 4\r\n\r\nabcd".toUTF8),
    ("-1: fails, and the connection is not reused", clientRead "HTTP/1.1 200 OK\r\nContent-Length: -1\r\n\r\n".toUTF8
      |>.assert hasFailed "expected a failure" |>.assertNotKeepAlive |>.run),
    ("TE chunked with CL", expectFailed "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\nContent-Length: 5\r\n\r\n5\r\nhello\r\n0\r\n\r\n".toUTF8),
    ("204 with differing CLs ends at the head", clientRead "HTTP/1.1 204 No Content\r\nContent-Length: 3\r\nContent-Length: 4\r\n\r\n".toUTF8
      |>.assertNoError |>.drainBody |>.assertPulledBody .empty |>.assertReaderComplete |>.run),
    ("304 with differing CLs ends at the head", clientRead "HTTP/1.1 304 Not Modified\r\nContent-Length: 3\r\nContent-Length: 4\r\n\r\n".toUTF8
      |>.assertNoError |>.drainBody |>.assertPulledBody .empty |>.assertReaderComplete |>.run)
  ] (·.2)

-- RFC 9112 §8: an incomplete response delivers what arrived, then fails. `…0\r\n` then EOF waits for P2.
#eval checkCases "Truncated responses" #[
    ("CL 123 with 26 bytes", "HTTP/1.1 200 OK\r\nContent-Length: 123\r\n\r\n", "abcdefghijklmnopqrstuvwxyz"),
    ("CL 10 with 7 bytes", "HTTP/1.1 200 OK\r\nContent-Length: 10\r\n\r\n", "1234567"),
    ("chunked, cut before the last chunk", "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n", "")
  ] fun (label, head, part) => do
    let t := clientRead (head ++ part).toUTF8 |>.drainBody |>.noMoreInput |>.drainBody |>.step
    let want := if label.startsWith "chunked" then "hello" else part
    let got := t.pulled.foldl (fun acc c => acc ++ c.chunk.data) .empty
    ensure (got == want.toUTF8) s!"delivered {(String.fromUTF8! got).quote}"
    ensure (t.machine.error == some .connectionClosed) s!"expected connectionClosed, got {repr t.machine.error}"

#eval checkCases "A status line without CRLF, then EOF" #[
    ("HTTP/1.1 200 Ok", clientRead "HTTP/1.1 200 Ok".toUTF8 |>.noMoreInput |>.step
      |>.assertFailedWith .connectionClosed |>.run)
  ] (·.2)

-- RFC 9112 §6.3 rule 1: HEAD, 204 and 304 responses end at the head.
#eval checkCases "Bodyless responses whatever their framing fields" #[
    ("HEAD, CL 100", "HTTP/1.1 200 OK\r\nContent-Length: 100\r\n\r\n", Method.head),
    ("HEAD, chunked", "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n", .head),
    ("204, CL 100", "HTTP/1.1 204 No Content\r\nContent-Length: 100\r\n\r\n", .get),
    ("204, chunked", "HTTP/1.1 204 No Content\r\nTransfer-Encoding: chunked\r\n\r\n", .get),
    ("304, CL 100", "HTTP/1.1 304 Not Modified\r\nContent-Length: 100\r\n\r\n", .get),
    ("304, chunked", "HTTP/1.1 304 Not Modified\r\nTransfer-Encoding: chunked\r\n\r\n", .get),
    ("HEAD, chunked, then chunk bytes", "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n0\r\n\r\n", .head)
  ] fun (_, raw, method) =>
    clientRead raw.toUTF8 { minimalGetRequest with method } |>.assertNoError |>.drainBody
      |>.assertPulledBody .empty |>.assertReaderComplete |>.run

-- RFC 9112 §6.3 rule 8: no framing means the body runs to EOF; leftover bytes wait for the next response.
#eval checkCases "Responses without framing, and bytes after a complete response" #[
    ("HTTP/1.0, no CL or TE", clientRead "HTTP/1.0 200 OK\r\n\r\n".toUTF8 |>.assertNoError |>.assertNotKeepAlive
      |>.feed "to eof" |>.noMoreInput |>.drainBody |>.assertPulledBody "to eof".toUTF8 |>.assertLastChunkFinal |>.run),
    ("bytes after a CL response stay unread", clientRead "HTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\nokEXTRA".toUTF8
      |>.drainBody |>.assertPulledBody "ok".toUTF8
      |>.assert (·.reader.input.remainingBytes == 5) "expected the 5 extra bytes unread" |>.run),
    ("bytes after a chunked response stay unread", clientRead "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n2\r\nok\r\n0\r\n\r\nEXTRA".toUTF8
      |>.drainBody |>.assertPulledBody "ok".toUTF8
      |>.assert (·.reader.input.remainingBytes == 5) "expected the 5 extra bytes unread" |>.run)
  ] (·.2)

private def connectHead : Request.Head :=
  { method := .connect, version := .v11, uri := RequestTarget.parse! "example.com:443",
    headers := Headers.empty.insert! "Host" "example.com:443" }

-- RFC 9112 §6.3 rule 2: a client MUST ignore framing fields in a 2xx response to CONNECT.
#eval checkCases "2xx to CONNECT ends at the head" #[
    ("Content-Length: 5", "Content-Length: 5\r\n"), ("Transfer-Encoding: chunked", "Transfer-Encoding: chunked\r\n"),
    ("no framing", "")
  ] fun (_, framing) =>
    clientRead s!"HTTP/1.1 200 OK\r\n{framing}\r\n\x16\x03\x01tunnel bytes".toUTF8 connectHead
      |>.assertNoError |>.drainBody |>.assertPulledBody .empty |>.assertReaderComplete |>.run

/-! ## Response trailers (RFC 9110 §6.5) -/

#eval checkCases "Response trailers: machine" #[
    ("§6.5: forbidden non-framing trailer field in a response is dropped", do
      -- §6.5.1: a client drops a trailer field it must not process instead of failing the response
      MachineTester.sending "§6.5: forbidden non-framing trailer field in a response is dropped"
        |>.send minimalGetRequest |>.step
        |>.feed "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n2\r\nok\r\n0\r\nCache-Control: no-cache\r\n\r\n"
        |>.step |>.assertNoError
        |>.drainBody |>.assertNoError |>.assertPulledBody "ok".toUTF8 |>.assertLastChunkFinal |>.run),
    ("§6.5: framing field in response trailers → badMessage", do
      -- a field that frames the message is still refused in a response's trailers
      MachineTester.sending "§6.5: framing field in response trailers → badMessage"
        |>.send minimalGetRequest |>.step
        |>.feed "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n2\r\nok\r\n0\r\nContent-Length: 2\r\n\r\n"
        |>.step |>.drainBody |>.assertFailedWith .badMessage |>.run)
  ] (·.2)

/-! ## Interim and upgrade (RFC 9110 §15.2) -/

#eval checkCases "Interim and upgrade: machine" #[
    ("§15.2: multiple 1xx responses all skipped", do
      -- §15.2: multiple 1xx responses before the real response are all skipped
      MachineTester.sending "§15.2: multiple 1xx responses all skipped"
        |>.send minimalGetRequest |>.step
        |>.feed "HTTP/1.1 100 Continue\r\n\r\n" |>.step
        |>.feed "HTTP/1.1 102 Processing\r\n\r\n" |>.step
        |>.feed "HTTP/1.1 200 OK\r\nContent-Length: 0\r\n\r\n" |>.step
        |>.assertNoError
        |>.onEndHeaders (fun t head =>
          if head.status != .ok then
            t.addError s!"expected 200 OK after 1xx chain, got {repr head.status}"
          else t)
        |>.run),
    ("§15.2: 103 Early Hints → no closeBody until the final response", do
      -- §15.2: an interim response has no body of its own, so it must not end the response body
      MachineTester.sending "§15.2: 103 Early Hints → no closeBody until the final response"
        |>.send minimalGetRequest |>.step
        |>.feed "HTTP/1.1 103 Early Hints\r\nLink: </style.css>; rel=preload\r\n\r\n" |>.step
        |>.assertNoError
        |>.assertNoEvent (fun | .closeBody => true | _ => false)
            "an interim response must not emit closeBody"
        |>.feed "HTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\nok" |>.step
        |>.drainBody |>.assertNoError |>.assertPulledBody "ok".toUTF8
        |>.assertHasCloseBody |>.run),
    ("§15.2.2: 101 Switching Protocols ends the exchange", do
      -- §15.2.2: after 101 the connection speaks the new protocol, so no final response follows and the
      -- bytes after the head are not read as HTTP
      MachineTester.sending "§15.2.2: 101 Switching Protocols ends the exchange"
        |>.send { minimalGetRequest with
          headers := minimalGetRequest.headers
            |>.insert! "Connection" "upgrade" |>.insert! "Upgrade" "websocket" }
        |>.step
        |>.feed "HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\n\r\n"
        |>.feedBytes (ByteArray.mk #[0x81, 0x02, 0x68, 0x69])
        |>.step
        |>.assertNoError |>.assertHasEndHeaders |>.assertNotKeepAlive
        |>.assertReaderClosed |>.run)
  ] (·.2)


-- RFC 9112 §8: a connection that closes before a final response is an incomplete exchange.
#eval checkCases "EOF without a final response" #[
    ("before any status line", MachineTester.sending "before any status line"
      |>.send minimalGetRequest |>.step |>.noMoreInput |>.step
      |>.assert hasFailed "expected a failure, not a normal end" |>.run),
    ("after only 100 Continue", clientRead "HTTP/1.1 100 Continue\r\n\r\n".toUTF8 |>.noMoreInput |>.step
      |>.assert hasFailed "expected a failure, not a normal end" |>.run)
  ] (·.2)

/-! ## Request heads (RFC 9112 §3, §6.1) -/

#eval checkCases "Request heads: machine" #[
    ("§6.1: client keeps the caller's Transfer-Encoding: gzip, chunked", do
      MachineTester.sending "§6.1: client keeps the caller's Transfer-Encoding: gzip, chunked"
        |>.send { minimalGetRequest with
          method := .post, headers := minimalGetRequest.headers.insert! "Transfer-Encoding" "gzip, chunked" }
        |>.sendBytes "abc".toUTF8 |>.userClosedBody |>.step
        |>.assertOutputContains "Transfer-Encoding: gzip, chunked\r\n" "expected the caller's codings"
        |>.assertOutputContains "3\r\nabc\r\n0\r\n\r\n" "expected a chunked body" |>.run)
  ] (·.2)

#eval checkCases "Request heads: async_http_h1_client_request_version.lean" #[
    ("show IO Unit from do",
      show IO Unit from do
      let late := secondRequest .empty
      let early := secondRequest "HTTP/1.0 200 OK\r\n".toUTF8
      unless late == early do
        throw <| IO.userError s!"request head changed: {(String.fromUTF8! late).quote} vs {(String.fromUTF8! early).quote}"
      unless late == "HEAD / HTTP/1.1\r\nHost: a\r\n\r\n".toUTF8 do
        throw <| IO.userError s!"unexpected request head: {(String.fromUTF8! late).quote}")
  ] (·.2)

#eval checkCases "Request heads: async_http_uri_rendering.lean" #[
    ("On the wire, the target reads back as a request-target.",
      show IO Unit from do
      let absolute := RequestTarget.absoluteForm (URI.parse! "http://user:secret@example.com/x?q#frag")
      let headers := Headers.empty.insert Header.Name.host (.mk "example.com")
      let head : Request.Head := { method := .get, version := .v11, uri := absolute, headers }
      let m : Machine .sending := { config := {} }
      let (_, out) := run (m.setKnownSize (.fixed 0) |>.send head |>.userClosedBody)
      expect (out.startsWith "GET http://example.com/x?q HTTP/1.1\x0d\n") s!"request line {out.quote}")
  ] (·.2)

/-! ## Request body framing (RFC 9112 §6, RFC 9110 §8.6) -/

#eval checkCases "Request body framing: machine" #[
    ("§8.6: bodyless GET request carries no Content-Length", do
      -- RFC 9110 §8.6: no Content-Length on a request without content whose method anticipates none
      MachineTester.sending "§8.6: bodyless GET request carries no Content-Length"
        |>.send minimalGetRequest |>.userClosedBody |>.step
        |>.assertOutputStartsWith "GET / HTTP/1.1\r\n" "expected the request line"
        |>.assertOutputNotContains "Content-Length" "a bodyless GET must not carry Content-Length" |>.run),
    ("§8.6: bodyless POST request still carries Content-Length: 0", do
      MachineTester.sending "§8.6: bodyless POST request still carries Content-Length: 0"
        |>.send { minimalGetRequest with method := .post } |>.userClosedBody |>.step
        |>.assertOutputContains "Content-Length: 0\r\n" "a bodyless POST keeps Content-Length: 0" |>.run),
    ("§8.6: a GET whose caller set Content-Length: 0 keeps it", do
      MachineTester.sending "§8.6: a GET whose caller set Content-Length: 0 keeps it"
        |>.send { minimalGetRequest with headers := minimalGetRequest.headers.insert! "Content-Length" "0" }
        |>.userClosedBody |>.step
        |>.assertOutputContains "Content-Length: 0\r\n" "an explicit framing field is kept" |>.run)
  ] (·.2)

#eval checkCases "Request body framing: async_http_h1_framing_mismatch.lean" #[
    ("Client side: a request declaring 10 bytes for a 3-byte body ends the exchange unwritten.",
      show IO Unit from do
      -- Client side: a request declaring 10 bytes for a 3-byte body ends the exchange unwritten.
      let request : Request.Head :=
        (Request.new |>.method .put |>.uri! "/upload" |>.header! "Host" "example.com"
          |>.header! "Content-Length" "10").line
      let machine := ({ config := {} } : Machine .sending)
        |>.setKnownSize (.fixed 3)
        |>.send request
        |>.sendData abc |>.userClosedBody
      let some (out, events) := runToHalt machine
        | throw <| IO.userError "the client never halted"
      unless out.isEmpty && events.any (· matches .failed (.other _)) do
        throw <| IO.userError s!"client: expected a failure and no output, got {repr events}\n{out.quote}"

      -- A streamed upload takes its length from the request's `Content-Length`.
      let request : Request.Head :=
        (Request.new |>.method .put |>.uri! "/upload" |>.header! "Host" "example.com"
          |>.header! "Content-Length" "3").line
      let machine := ({ config := {} } : Machine .sending)
        |>.setKnownSize .chunked
        |>.send request
        |>.sendData abc |>.userClosedBody
      let mut machine := machine
      let mut out := ""
      for _ in [0:8] do
        let (next, step) := machine.step
        machine := next
        out := out ++ String.fromUTF8! step.output.toByteArray
      unless out.contains "Content-Length: 3\r\n" && !out.contains "Transfer-Encoding" &&
          out.endsWith "\r\n\r\nabc" && machine.error.isNone do
        throw <| IO.userError s!"streamed upload: got {repr machine.error}\n{out.quote}")
  ] (·.2)

#eval checkCases "Request body framing: async_http_h1_short_fixed_body.lean" #[
    ("Client side: the request body ends after 5 of its 10 declared bytes.",
      show IO Unit from do
      let machine : Machine .sending := { config := {} }
      let machine := machine.send putHead
        |>.sendData #[Chunk.ofByteArray "12345".toUTF8] |>.userClosedBody
      unless ← closesWhenWriting machine "12345" do
        throw <| IO.userError "a request body 5 bytes short was not reported in the step that wrote it"),
    ("Control: the whole declared body completes the message without an error.",
      show IO Unit from do
      let machine : Machine .sending := { config := {} }
      let mut machine := machine.send putHead
        |>.sendData #[Chunk.ofByteArray "0123456789".toUTF8] |>.userClosedBody
      for _ in [0:8] do
        let (next, _) := machine.step
        machine := next
      if machine.error.isSome then
        throw <| IO.userError s!"a complete body failed with {machine.error.map toString}")
  ] (·.2)

#eval checkCases "Request body framing: async_http_h1_v10_framing.lean" #[
    ("Control: an HTTP/1.1 request of unknown length streams chunked.",
      show IO Unit from do
      let (_, out) := sendLateBody .v10
      expect (!out.contains "Transfer-Encoding" && out.contains "Content-Length: 5\x0d\n"
          && out.endsWith "\x0d\n\x0d\nhello")
        s!"client HTTP/1.0 POST of unknown length: {out.quote}"
      -- Control: an HTTP/1.1 request of unknown length streams chunked.
      let (_, out) := sendLateBody .v11
      expect (out.contains "Transfer-Encoding: chunked") s!"client HTTP/1.1 POST of unknown length: {out.quote}"),
    ("A length set as `chunked` cannot be sent over HTTP/1.0: the exchange ends with nothing written.",
      show IO Unit from do
      let m : Machine .sending := { config := {} }
      let (m, out) := run (m.setKnownSize .chunked |>.send (post .v10)
        |>.sendData #[Chunk.ofByteArray "hello".toUTF8] |>.userClosedBody)
      expect (out.isEmpty && m.error.isSome)
        s!"client HTTP/1.0 POST set as chunked: expected nothing written and an error, got {out.quote}")
  ] (·.2)


private def methodHead (method : Method) : Request.Head :=
  if method == .connect then connectHead else { minimalGetRequest with method }

-- RFC 9110 §8.6: a request without content carries `Content-Length: 0` only if its method expects content.
#eval checkCases "Bodyless requests" #[
    ("GET", Method.get, false), ("HEAD", .head, false), ("DELETE", .delete, false),
    ("OPTIONS", .options, false), ("TRACE", .trace, false), ("CONNECT", .connect, false),
    ("POST", .post, true), ("PUT", .put, true), ("PATCH", .patch, true)
  ] fun (_, method, zero) => do
    let t := MachineTester.sending "bodyless" |>.send (methodHead method) |>.userClosedBody |>.step
    let out := String.fromUTF8! t.allOutput
    ensure (out.contains "Content-Length: 0\r\n" == zero && (zero || !out.contains "Content-Length")) s!"{out.quote}"
