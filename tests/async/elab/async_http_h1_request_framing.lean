module

import Std.Http.Test.Helpers
import Std.Http.Test.Machine

/-!
# HTTP/1.1 request framing

What a server accepts as a request body: `Content-Length`, `Transfer-Encoding`, chunked syntax, chunk
extensions, trailers, truncated bodies and smuggling vectors. Each rule has its machine table next to
its `serveConnection` table. RFC 9112 §6, §7; RFC 9110 §5.3, §6.5, §8.6. Regressions: #16362.
Request trailers that carry a field forbidden in trailers are rejected with 400; RFC 9112 §7.1.2
would also allow discarding them, so this is Std.Http policy.
-/

open Std Http
open Std.Async
open Std.Http.Protocol.H1
open Std.Http.Internal.Test

private def mkPostHead (path : String) (bodyLen : Nat) (extra : String := "") : String :=
  rawRequest "POST" path (extra := s!"Content-Length: {bodyLen}\r\n{extra}")

private def mkChunkedPost (path : String) (extra : String := "") : String :=
  rawRequest "POST" path (extra := s!"Transfer-Encoding: chunked\r\n{extra}")

/-- `(label, raw, handler, want, config)` rows served without closing the input. -/
private def expectServer (raw : String) (handler : TestHandler) (want : Want)
    (config : Std.Http.Config := testConfig) (closeInput : Bool := false) : IO Unit :=
  checkHandler raw handler want config closeInput

/-- The trailer tests ran with a 3-second lingering timeout. -/
private def trailerConfig : Std.Http.Config := { lingeringTimeout := 3000, generateDate := false }

/-- A `Transfer-Encoding` field value as the handler sees it, then the body. -/
private def teAndBody : TestHandler := fun req => do
  let te := match req.line.headers.getAll? Header.Name.transferEncoding with
    | some vs => String.intercalate "|" (vs.map (fun (v : Header.Value) => v.value) |>.toList)
    | none => "<none>"
  let body : String ← req.body.readAll
  Response.ok |>.text s!"{te};{body}"

private def ok200 : Want := .all [.status "HTTP/1.1 200", .contains "hello"]

/-! ## Content-Length (RFC 9110 §8.6, RFC 9112 §6.3) -/

#eval checkCases "RFC 9112 §6.3: body framing: machine" #[
    ("§6.3: no CL/TE → empty body", MachineTester.receiving "§6.3: no CL/TE → empty body"
      |>.feed (mkGet "/")
      |>.step |>.assertNoError |>.assertHasEndHeaders
      |>.assertCanPullBodyNow |>.drainBody
      |>.assertPulledBody .empty |>.assertLastChunkFinal |>.run),
    ("§6.3: Content-Length body delivered exactly", do
      let body := "Hello, World!".toUTF8
      MachineTester.receiving "§6.3: Content-Length body delivered exactly"
        |>.feed (mkPostHead "/" body.size ++ String.fromUTF8! body)
        |>.step |>.assertNoError |>.assertHasEndHeaders
        |>.drainBody |>.assertPulledBody body |>.assertLastChunkFinal |>.run),
    ("§6.3: multiple Content-Length → badMessage", MachineTester.receiving "§6.3: multiple Content-Length → badMessage"
      |>.feed "POST / HTTP/1.1\r\nHost: example.com\r\nContent-Length: 5\r\nContent-Length: 5\r\n\r\n"
      |>.step |>.assertFailedWith .badMessage |>.run),
    ("§6.3: fixed-length body stops at declared byte count", MachineTester.receiving "§6.3: fixed-length body stops at declared byte count"
      |>.feed (mkPostHead "/" 5 ++ "helloworld")
      |>.step |>.assertHasEndHeaders
      |>.drainBody
      |>.assertPulledBody "hello".toUTF8
      |>.assertLastChunkFinal |>.assertNoError |>.run)
  ] (·.2)

#eval checkCases "RFC 9112 §6.3: Content-Length: server" #[
    ("CL body accepted and echoed", mkPost "/echo" "hello" "Connection: close\x0d\n", ok200),
    ("duplicate Content-Length same value → 400",
      "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 5\x0d\nContent-Length: 5\x0d\nConnection: close\x0d\n\x0d\nhello", .exact r400),
    ("duplicate Content-Length different values → 400",
      "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 3\x0d\nContent-Length: 5\x0d\nConnection: close\x0d\n\x0d\nabc", .exact r400),
    ("duplicate Content-Length 0, 0", "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 0\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\n\x0d\n", .exact r400),
    ("duplicate Content-Length 64, 64",
      s!"POST / HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 64\x0d\nContent-Length: 64\x0d\nConnection: close\x0d\n\x0d\n{String.ofList (List.replicate 64 'a')}", .exact r400),
    ("duplicate Content-Length 3, 4", "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 3\x0d\nContent-Length: 4\x0d\nConnection: close\x0d\n\x0d\nabc", .exact r400),
    ("duplicate Content-Length 54, 64",
      s!"POST / HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 54\x0d\nContent-Length: 64\x0d\nConnection: close\x0d\n\x0d\n{String.ofList (List.replicate 54 'a')}", .exact r400),
    ("non-numeric Content-Length → 400",
      "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: abc\x0d\nConnection: close\x0d\n\x0d\nbody", .exact r400),
    ("negative Content-Length → 400",
      "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: -1\x0d\nConnection: close\x0d\n\x0d\n", .exact r400),
    ("underscore in Content-Length → 400",
      "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 1_0\x0d\nConnection: close\x0d\n\x0d\n0123456789", .exact r400)
  ] fun (_, raw, want) => expectServer raw echoHandler want

-- The leading-zero table compares the exact echoed body.
#eval checkCases "Content-Length with leading zeros accepted" #[
    ("005", "005", "hello"),
    ("0005", "0005", "abcde"),
    ("00010", "00010", "0123456789"),
    ("0096", "0096", String.ofList (List.replicate 96 'z'))
  ] fun (_, cl, body) =>
    expectServer s!"POST / HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: {cl}\x0d\nConnection: close\x0d\n\x0d\n{body}"
      echoHandler (.body body)


private def clRequest (method : String) (fields : String) (body : String := "") : String :=
  s!"{method} / HTTP/1.1\x0d\nHost: example.com\x0d\n{fields}Connection: close\x0d\n\x0d\n{body}"

-- RFC 9110 §8.6: `Content-Length = 1*DIGIT`; RFC 9112 §6.3 rule 5: an invalid value is unrecoverable.
#eval checkCases "Content-Length forms" #[
    ("1 , 1,2", clRequest "POST" "Content-Length: 1 , 1,2\x0d\n" "a", Want.exact r400),
    ("empty", clRequest "POST" "Content-Length: \x0d\n", .exact r400),
    ("empty, then 3", clRequest "POST" "Content-Length: \x0d\nContent-Length: 3\x0d\n" "abc", .exact r400),
    ("+3", clRequest "POST" "Content-Length: +3\x0d\n" "abc", .exact r400), ("-3", clRequest "POST" "Content-Length: -3\x0d\n" "abc", .exact r400),
    ("yes", clRequest "POST" "Content-Length: yes\x0d\n" "abc", .exact r400), ("0x10", clRequest "POST" "Content-Length: 0x10\x0d\n" "abc", .exact r400),
    ("1x", clRequest "POST" "Content-Length: 1x\x0d\n" "abc", .exact r400), ("asdf", clRequest "POST" "Content-Length: asdf\x0d\n" "abc", .exact r400),
    ("HEAD with Content-Length 0", clRequest "HEAD" "Content-Length: 0\x0d\n", .status "HTTP/1.1 200"),
    -- RFC 9110 §9.3.2: the 400 to a HEAD request has no content.
    ("HEAD with Content-Length 4 and 5", clRequest "HEAD" "Content-Length: 4\x0d\nContent-Length: 5\x0d\n" "abcde",
      .all [.status "HTTP/1.1 400 Bad Request", .absent "\x0d\n\x0d\nBad Request"])
  ] fun (_, raw, want) => expectServer raw echoHandler want (closeInput := true)

/-! ## Transfer-Encoding (RFC 9112 §6.1, RFC 9110 §5.3) -/

/-- The field `Transfer-Encoding` of the head, which must be the single value `expected`. -/
private def teField (expected : String) (t : MachineTester .receiving) (head : Request.Head) :
    MachineTester .receiving :=
  match head.headers.getAll? Header.Name.transferEncoding with
  | some #[value] =>
    if value.value == expected then t
    else t.addError s!"expected Transfer-Encoding {expected.quote}, got {value.value.quote}"
  | _ => t.addError "expected one Transfer-Encoding field"

#eval checkCases "RFC 9112 §6: Transfer-Encoding validation: machine" #[
    -- RFC 9110 §5.3: the field lines of Transfer-Encoding form one list, so these are `gzip, chunked`
    ("§6.1: gzip and chunked on two field lines → unsupportedTransferCoding",
      MachineTester.receiving "§6.1: gzip and chunked on two field lines → unsupportedTransferCoding"
      |>.feed "POST / HTTP/1.1\r\nHost: example.com\r\nTransfer-Encoding: gzip\r\nTransfer-Encoding: chunked\r\n\r\n"
      |>.step |>.assertFailedWith .unsupportedTransferCoding |>.run),
    ("§6.1: chunked on two field lines is chunked applied twice → badMessage",
      MachineTester.receiving "§6.1: chunked on two field lines is chunked applied twice → badMessage"
      |>.feed "POST / HTTP/1.1\r\nHost: example.com\r\nTransfer-Encoding: chunked\r\nTransfer-Encoding: chunked\r\n\r\n"
      |>.step |>.assertFailedWith .badMessage |>.run),
    -- RFC 9110 §5.6.1.2: empty list elements are ignored
    ("§6.1: accepted codings over two field lines with empty elements",
      MachineTester.receiving "§6.1: accepted codings over two field lines with empty elements"
        (config := { acceptedTransferCodings := #["gzip"] })
      |>.feed ("POST / HTTP/1.1\r\nHost: example.com\r\nTransfer-Encoding: gzip, \r\n" ++
        "Transfer-Encoding: , chunked\r\n\r\n3\r\nabc\r\n0\r\n\r\n")
      |>.step |>.assertNoError
      |>.drainBody |>.assertNoError |>.assertPulledBody "abc".toUTF8 |>.assertLastChunkFinal |>.run),
    ("§6.1: Transfer-Encoding: gzip, , chunked → unsupportedTransferCoding",
      MachineTester.receiving "§6.1: Transfer-Encoding: gzip, , chunked → unsupportedTransferCoding"
      |>.feed "POST / HTTP/1.1\r\nHost: example.com\r\nTransfer-Encoding: gzip, , chunked\r\n\r\n"
      |>.step |>.assertFailedWith .unsupportedTransferCoding |>.run),
    ("§6.1: Transfer-Encoding: identity → badMessage", MachineTester.receiving "§6.1: Transfer-Encoding: identity → badMessage"
      |>.feed "POST / HTTP/1.1\r\nHost: example.com\r\nTransfer-Encoding: identity\r\n\r\n"
      |>.step |>.assertFailedWith .badMessage |>.run),
    -- §6.3 rule 4: a request whose final coding is not `chunked` has no reliable length: 400, not 501
    ("§6.3: Transfer-Encoding: gzip request → badMessage", MachineTester.receiving "§6.3: Transfer-Encoding: gzip request → badMessage"
      |>.feed "POST / HTTP/1.1\r\nHost: example.com\r\nTransfer-Encoding: gzip\r\n\r\nabc"
      |>.step |>.assertFailedWith .badMessage |>.run),
    -- §6.1: a coding the application decodes itself is accepted; the machine removes only the
    -- chunked framing and keeps the field that says which codings are left
    ("§6.1: accepted gzip;level=1, chunked → body still coded, field kept",
      MachineTester.receiving "§6.1: accepted gzip;level=1, chunked → body still coded, field kept"
        (config := { acceptedTransferCodings := #["gzip"] })
      |>.feed ("POST / HTTP/1.1\r\nHost: example.com\r\nTransfer-Encoding: gzip;level=1, chunked\r\n\r\n" ++
        "3\r\nabc\r\n0\r\n\r\n")
      |>.step |>.assertNoError |>.onEndHeaders (teField "gzip;level=1, chunked")
      |>.drainBody |>.assertNoError |>.assertPulledBody "abc".toUTF8 |>.assertLastChunkFinal |>.run),
    ("§6.1: accepted coding names are compared case-insensitively",
      MachineTester.receiving "§6.1: accepted coding names are compared case-insensitively"
        (config := { acceptedTransferCodings := #["GZIP"] })
      |>.feed ("POST / HTTP/1.1\r\nHost: example.com\r\nTransfer-Encoding: Gzip, Chunked\r\n\r\n" ++
        "3\r\nabc\r\n0\r\n\r\n")
      |>.step |>.assertNoError |>.onEndHeaders (teField "Gzip, Chunked")
      |>.drainBody |>.assertNoError |>.assertPulledBody "abc".toUTF8 |>.run),
    ("§6.1: every coding before chunked must be accepted",
      MachineTester.receiving "§6.1: every coding before chunked must be accepted"
        (config := { acceptedTransferCodings := #["gzip"] })
      |>.feed ("POST / HTTP/1.1\r\nHost: example.com\r\nTransfer-Encoding: br, gzip, chunked\r\n\r\n" ++
        "3\r\nabc\r\n0\r\n\r\n")
      |>.step |>.assertFailedWith .unsupportedTransferCoding |>.run),
    -- §6.3 rule 4: an accepted coding does not give a request without a final chunked a length
    ("§6.3: accepted gzip without chunked → badMessage",
      MachineTester.receiving "§6.3: accepted gzip without chunked → badMessage"
        (config := { acceptedTransferCodings := #["gzip"] })
      |>.feed "POST / HTTP/1.1\r\nHost: example.com\r\nTransfer-Encoding: gzip\r\n\r\nabc"
      |>.step |>.assertFailedWith .badMessage |>.run),
    -- RFC 9112 §7.1: `chunked` defines no parameters
    ("§7: Transfer-Encoding: chunked;x=1 request → badMessage",
      MachineTester.receiving "§7: Transfer-Encoding: chunked;x=1 request → badMessage"
      |>.feed "POST / HTTP/1.1\r\nHost: example.com\r\nTransfer-Encoding: chunked;x=1\r\n\r\n0\r\n\r\n"
      |>.step |>.assertFailedWith .badMessage |>.run),
    ("RFC 9112 §6.1: chunked TE on HTTP/1.0 → badMessage", MachineTester.receiving "RFC 9112 §6.1: chunked TE on HTTP/1.0 → badMessage"
      |>.feed "POST / HTTP/1.0\r\nTransfer-Encoding: chunked\r\n\r\n"
      |>.step |>.assertFailedWith .badMessage |>.run)
  ] (·.2)

-- §6.1: a server answers a transfer coding it does not understand with 501; only `chunked` is
-- decoded, so any other coding before it is not implemented.
#eval checkCases "RFC 9112 §6.1: unknown codings → 501: machine" #[
    "gzip, chunked", "br, chunked", "gzip;level=1, chunked", "x-custom, gzip, chunked"
  ] fun coding =>
    MachineTester.receiving s!"§6.1: Transfer-Encoding: {coding} request → 501 Not Implemented"
      |>.feed (s!"POST / HTTP/1.1\r\nHost: example.com\r\nTransfer-Encoding: {coding}\r\n\r\n" ++
        "3\r\nabc\r\n0\r\n\r\n")
      |>.step |>.assertFailedWith .unsupportedTransferCoding
      |>.step
      |>.assertOutputStartsWith "HTTP/1.1 501 Not Implemented\r\n" "expected 501"
      |>.assertOutputContains "Connection: close\r\n" "the unread body ends the connection" |>.run

#eval checkCases "RFC 9112 §6.1: Transfer-Encoding validation: server" #[
    ("TE: chunked not last (chunked, gzip) → 400", "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked, gzip\x0d\nConnection: close\x0d\n\x0d\nbody", okHandler, Want.exact r400, testConfig),
    ("TE: duplicate chunked → 400", "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked, chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n", okHandler, .exact r400, testConfig),
    ("TE: gzip alone (no chunked framing) → 400", "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: gzip\x0d\nConnection: close\x0d\n\x0d\nbody", okHandler, .exact r400, testConfig),
    ("TE: deflate alone → 400", "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: deflate\x0d\nConnection: close\x0d\n\x0d\nbody", okHandler, .exact r400, testConfig),
    ("TE: identity alone → 400", "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: identity\x0d\nConnection: close\x0d\n\x0d\nbody", okHandler, .exact r400, testConfig),
    -- RFC 9110 §5.6.1.2: a recipient ignores empty list elements
    ("TE: empty list element before chunked is ignored", "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: ,chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n", echoHandler, ok200, testConfig),
    -- RFC 9110 §5.3: the field lines combine into `chunked, gzip`, whose final coding is not chunked
    ("TE: field lines chunked then gzip → 400",
      "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nTransfer-Encoding: gzip\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n",
      echoHandler, .exact r400, testConfig),
    ("NUL byte in TE value → 400", "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunk\x00ed\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n", okHandler, .exact r400, testConfig),
    ("control char (0x01) in TE value → 400", "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunk\x01ed\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n", okHandler, .exact r400, testConfig),
    -- §6.1: only `chunked` is decoded, so the handler never sees a body still coded with another coding
    ("gzip, chunked → 501, handler not run", "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: gzip, chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n", echoHandler, .exact r501, testConfig),
    -- RFC 9110 §5.3: the same codings over two field lines are the same list
    ("gzip and chunked on two field lines → 501",
      "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: gzip\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n",
      echoHandler, .exact r501, testConfig),
    ("br, chunked → 501", "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: br, chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n", echoHandler, .exact r501, testConfig),
    -- A coding the handler decodes itself reaches it with the chunked framing removed and the field
    -- that names the codings left (#16362)
    ("gzip, chunked accepted when listed in acceptedTransferCodings", "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: gzip, chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n",
      teAndBody, .all [.status "HTTP/1.1 200", .contains "gzip, chunked;hello"],
      { testConfig with acceptedTransferCodings := #["gzip"] }),
    ("gzip and chunked on two field lines accepted when gzip is listed",
      "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: gzip\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n",
      echoHandler, ok200, { testConfig with acceptedTransferCodings := #["gzip"] }),
    ("br, chunked → 501 when only gzip is accepted", "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: br, chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n",
      echoHandler, .exact r501, { testConfig with acceptedTransferCodings := #["gzip"] }),
    ("mixed-case Chunked accepted (codings are lowercased)", "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: Chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n", echoHandler, ok200, testConfig),
    ("TE trailing OWS accepted", "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked \x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n", echoHandler, .status "HTTP/1.1 200", testConfig),
    -- RFC 9110 §5.6.3: HTAB is optional whitespace before a field value.
    ("Transfer-Encoding: HTAB before chunked", "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding:\x09chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n",
      okHandler, .status "HTTP/1.1 200", testConfig)
  ] fun (_, raw, handler, want, config) => expectServer raw handler want config


-- RFC 9112 §6.3 rule 4: a request whose final coding is not chunked gets 400 and a close.
#eval checkCases "Transfer-Encoding values that do not frame the request" #[
    ("fugazi", "Transfer-Encoding: fugazi\x0d\n"), ("chunked, smooth", "Transfer-Encoding: chunked, smooth\x0d\n"),
    ("chunked, identity", "Transfer-Encoding: chunked, identity\x0d\n"),
    ("chunked, then identity on a second line", "Transfer-Encoding: chunked\x0d\nTransfer-Encoding: identity\x0d\n"),
    ("empty", "Transfer-Encoding: \x0d\n"), ("quoted", "Transfer-Encoding: \" chunked\"\x0d\n"),
    ("VT before chunked", "Transfer-Encoding: \x0bchunked\x0d\n")
  ] fun (_, te) =>
    expectServer s!"POST / HTTP/1.1\x0d\nHost: example.com\x0d\n{te}Connection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n"
      echoHandler (.exact r400) (closeInput := true)

-- RFC 9112 §6.1: HTTP/1.0 has no chunked coding, so TE with CL is faulty framing.
#eval checkCases "HTTP/1.0 with Transfer-Encoding, Content-Length and keep-alive" #[
    ("400, then close", do
      let (r, seen) ← serveRecording ("POST / HTTP/1.0\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\n" ++
        "Content-Length: 5\x0d\nConnection: keep-alive\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\nGET /next HTTP/1.0\x0d\n\x0d\n")
      ensure seen.isEmpty s!"the handler ran: {repr seen}"
      (Want.exact r400).check r)
  ] (·.2)

/-! ## Chunked syntax (RFC 9112 §7.1) -/

#eval checkCases "RFC 9112 §7.1: chunked transfer encoding: machine" #[
    ("§7.1: chunked TE decoded to raw body", MachineTester.receiving "§7.1: chunked TE decoded to raw body"
      |>.feed (mkChunkedPost "/" ++ "5\r\nhello\r\n5\r\nworld\r\n0\r\n\r\n")
      |>.step |>.assertNoError |>.assertHasEndHeaders
      |>.drainBody |>.assertPulledBody "helloworld".toUTF8 |>.assertLastChunkFinal |>.run),
    ("§7.1: empty chunked body", MachineTester.receiving "§7.1: empty chunked body"
      |>.feed (mkChunkedPost "/" ++ "0\r\n\r\n")
      |>.step |>.assertNoError
      |>.drainBody |>.assertPulledBody .empty |>.assertLastChunkFinal |>.run)
  ] (·.2)

#eval checkCases "RFC 9112 §7.1: chunked bodies and chunk sizes: server" #[
    ("chunked body accepted and echoed", mkChunked "/" (chunk "hello" ++ chunkEnd) "Connection: close\x0d\n", ok200, false),
    ("chunk-size uppercase and leading zeros accepted", "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n000A\x0d\n0123456789\x0d\n0\x0d\n\x0d\n",
      .all [.status "HTTP/1.1 200", .contains "0123456789"], false),
    ("chunk size 00000000000000005", mkChunked "/" "00000000000000005\x0d\nhello\x0d\n0\x0d\n\x0d\n",
      .all [.status "HTTP/1.1 200", .contains "\x0d\n\x0d\nhello"], true),
    ("chunk size with 40 leading zeros", mkChunked "/" s!"{String.join (List.replicate 40 "0")}5\x0d\nhello\x0d\n0\x0d\n\x0d\n",
      .all [.status "HTTP/1.1 200", .contains "\x0d\n\x0d\nhello"], true),
    -- Control: 17 significant digits are still too large.
    ("chunk size 10000000000000000", mkChunked "/" "10000000000000000\x0d\nhello\x0d\n", .status "HTTP/1.1 400", true),
    ("chunk size ffffffffffffffff1", mkChunked "/" "ffffffffffffffff1\x0d\nhello\x0d\n0\x0d\n\x0d\n", .exact r400, true),
    ("chunk terminator must be CRLF → 400", "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n3\x0d\nxxx__1a\x0d\n", .exact r400, true),
    ("chunk-size trailing whitespace → 400", "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5 \x0d\nhello\x0d\n0\x0d\n\x0d\n", .exact r400, false)
  ] fun (_, raw, want, closeInput) => expectServer raw echoHandler want (closeInput := closeInput)

#eval checkCases "invalid chunk-size token → 400" #[
    ("G", "G\x0d\nabc\x0d\n0\x0d\n\x0d\n"),
    ("g", "g\x0d\nabc\x0d\n0\x0d\n\x0d\n"), ("z", "z\x0d\nabc\x0d\n0\x0d\n\x0d\n"), ("Z", "Z\x0d\nabc\x0d\n0\x0d\n\x0d\n"),
    ("@", "@\x0d\nabc\x0d\n0\x0d\n\x0d\n"), ("!", "!\x0d\nabc\x0d\n0\x0d\n\x0d\n"), ("x", "x\x0d\nabc\x0d\n0\x0d\n\x0d\n"),
    ("GG", "GG\x0d\nhello\x0d\n0\x0d\n\x0d\n")
  ] fun (_, chunked) => expectServer ("POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n" ++ chunked) echoHandler (.exact r400)


#eval checkCases "Chunk-size table: server" #[
    ("aA is 170", s!"aA\x0d\n{String.ofList (List.replicate 170 'x')}\x0d\n0\x0d\n\x0d\n", Want.body (String.ofList (List.replicate 170 'x'))),
    ("ffffffffffffffff is too large", "ffffffffffffffff\x0d\nhello\x0d\n0\x0d\n\x0d\n", .status "HTTP/1.1 413"),
    ("100 digits", s!"{String.ofList (List.replicate 100 '1')}\x0d\nhello\x0d\n0\x0d\n\x0d\n", .exact r400),
    ("567xf8a", "567xf8a\x0d\nhello\x0d\n0\x0d\n\x0d\n", .exact r400), ("567f8a CR foo", "567f8a\x0dfoo\x0d\nhello\x0d\n0\x0d\n\x0d\n", .exact r400),
    ("0x5", "0x5\x0d\nhello\x0d\n0\x0d\n\x0d\n", .exact r400), ("an empty size line", "\x0d\nhello\x0d\n0\x0d\n\x0d\n", .exact r400),
    ("NUL after a valid size", "5\x00\x0d\nhello\x0d\n0\x0d\n\x0d\n", .exact r400)
  ] fun (_, chunked, want) =>
    expectServer ("POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n" ++ chunked)
      echoHandler want (closeInput := true)

-- The sizes exceed the default `maxChunkSize`; the machine is configured so only the syntax decides.
#eval checkCases "Chunk-size line syntax: machine" #[
    ("3735AB1;foo bar* → badMessage", MachineTester.receiving "3735AB1;foo bar*" { maxChunkSize := 1 <<< 30, maxBodySize := 1 <<< 30 }
      |>.feed (mkChunkedPost "/" ++ "3735AB1;foo bar*\r\nab") |>.step |>.pullBody
      |>.assertFailedWith .badMessage |>.run),
    ("3735ab1 ; baz is accepted", MachineTester.receiving "3735ab1 ; baz " { maxChunkSize := 1 <<< 30, maxBodySize := 1 <<< 30 }
      |>.feed (mkChunkedPost "/" ++ "3735ab1 ; baz \r\nab") |>.step |>.pullBody
      |>.assertNoError |>.assertPulledBody "ab".toUTF8 |>.run)
  ] (·.2)

-- RFC 9112 §7.1: chunk framing lines end in CRLF; RFC 9112 §2.2 leaves bare LF to the recipient.
#eval checkCases "Bare LF or stray CR in chunk framing" #[
    ("1 LF a", "1\na\x0d\n0\x0d\n\x0d\n"), ("1 CR CR LF a", "1\x0d\x0d\na\x0d\n0\x0d\n\x0d\n"),
    ("bare LF after the data", "1\x0d\na\n0\x0d\n\x0d\n"), ("1; LF a", "1;\na\x0d\n0\x0d\n\x0d\n"),
    ("0 CRLF LF", "0\x0d\n\n")
  ] fun (_, chunked) =>
    expectServer ("POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n" ++ chunked)
      echoHandler (.exact r400) (closeInput := true)

/-! ## Chunk extensions (RFC 9112 §7.1.1) -/

#eval checkCases "RFC 9112 §7.1.1: chunk extensions: machine" #[
    ("§7.1.1: chunk extensions preserved in PulledChunk", MachineTester.receiving "§7.1.1: chunk extensions preserved in PulledChunk"
      |>.feed (mkChunkedPost "/" ++ "5;quality=0.9\r\nhello\r\n0\r\n\r\n")
      |>.step |>.assertHasEndHeaders
      |>.drainBody |>.assertPulledBody "hello".toUTF8
      |>.onMachine (fun t _ =>
        match t.pulled[0]? with
        | none => t.addError "no chunks pulled"
        | some c =>
          let exts := c.chunk.extensions.map fun (n, v) => (n.value, v.map (·.value))
          if exts == #[("quality", some "0.9")] then t
          else t.addError s!"expected the extension quality=0.9, got {repr exts}")
      |>.run)
  ] (·.2)

#eval checkCases "RFC 9112 §7.1.1: chunk extensions: server" #[
    ("chunk extensions with token and quoted value accepted", "5;ext=val;quoted=\"ok\"\x0d\nhello\x0d\n0\x0d\n\x0d\n", ok200),
    ("extension with quoted-string value → accepted", "5;ext=\"hello world\"\x0d\nhello\x0d\n0\x0d\n\x0d\n", .status "HTTP/1.1 200"),
    ("multiple name=value extensions → accepted", "5;a=1;b=2;c=3\x0d\nhello\x0d\n0\x0d\n\x0d\n", .status "HTTP/1.1 200"),
    ("name-only extension (no value) → accepted", "5;novalue\x0d\nhello\x0d\n0\x0d\n\x0d\n", ok200),
    ("extension on terminal zero-chunk → accepted", "5\x0d\nhello\x0d\n0;final-ext=done\x0d\n\x0d\n", .status "HTTP/1.1 200"),
    ("non-token character in ext name → 400", "5;bad@name\x0d\nhello\x0d\n0\x0d\n\x0d\n", .exact r400)
  ] fun (_, chunked, want) => expectServer ("POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n" ++ chunked) echoHandler want

#eval checkCases "obs-text in a quoted chunk extension" #[
    ";n=\"é\"", ";n=\"a\\é\"", ";a=1;n=\"é\";b"
  ] fun ext =>
    expectServer (mkChunked "/" s!"5{ext}\x0d\nhello\x0d\n0\x0d\n\x0d\n") echoHandler
      (.all [.status "HTTP/1.1 200", .contains "\x0d\n\x0d\nhello"]) (closeInput := true)

/-! ## Trailers (RFC 9112 §7.1.2, RFC 9110 §6.5) -/

#eval checkCases "RFC 9110 §6.5: forbidden trailer fields: machine" #[
    ("§6.5: forbidden trailer field in a request → badMessage", MachineTester.receiving "§6.5: forbidden trailer field in a request → badMessage"
      |>.feed (mkChunkedPost "/" ++ "2\r\nok\r\n0\r\nCache-Control: no-cache\r\n\r\n")
      |>.step |>.drainBody |>.assertFailedWith .badMessage |>.run)
  ] (·.2)

#eval checkCases "Trailer fields: server" #[
    ("Single trailer header.", "5\x0d\nhello\x0d\n0\x0d\nChecksum: abc123\x0d\n\x0d\n", ok200),
    ("Multiple trailer headers.",
      "5\x0d\nhello\x0d\n0\x0d\nChecksum: abc123\x0d\nExpires: Thu, 01 Dec 1994 16:00:00 GMT\x0d\nX-Custom: value\x0d\n\x0d\n", ok200),
    ("Terminal chunk extensions can precede trailers.", "5\x0d\nhello\x0d\n0;ext=val\x0d\nX-Trailer: yes\x0d\n\x0d\n", ok200),
    ("Trailer syntax validation: no colon", "3\x0d\nabc\x0d\n0\x0d\nBadTrailer value\x0d\n\x0d\n", .exact r400),
    ("Trailer syntax validation: leading whitespace", "3\x0d\nabc\x0d\n0\x0d\n X-Bad: folded\x0d\n\x0d\n", .exact r400),
    ("Trailer syntax validation: space in name", "3\x0d\nabc\x0d\n0\x0d\nBad Name: value\x0d\n\x0d\n", .exact r400),
    ("Trailer byte-level validation: NUL in name", "3\x0d\nabc\x0d\n0\x0d\nX-Bad\x00Name: value\x0d\n\x0d\n", .exact r400),
    ("Trailer byte-level validation: NUL in value", "3\x0d\nabc\x0d\n0\x0d\nX-Header: bad\x00value\x0d\n\x0d\n", .exact r400),
    ("Trailer byte-level validation: 0x01 in value", "3\x0d\nabc\x0d\n0\x0d\nX-Header: bad\x01value\x0d\n\x0d\n", .exact r400),
    ("forbidden-field policy: content-length in trailer", "5\x0d\nhello\x0d\n0\x0d\nContent-Length: 1000\x0d\n\x0d\n", .exact r400),
    ("forbidden-field policy: transfer-encoding in trailer", "5\x0d\nhello\x0d\n0\x0d\nTransfer-Encoding: chunked\x0d\n\x0d\n", .exact r400),
    ("forbidden-field policy: host in trailer", "5\x0d\nhello\x0d\n0\x0d\nHost: evil.example\x0d\n\x0d\n", .exact r400),
    ("forbidden-field policy: connection in trailer", "5\x0d\nhello\x0d\n0\x0d\nConnection: keep-alive\x0d\n\x0d\n", .exact r400),
    ("forbidden-field policy: authorization in trailer", "5\x0d\nhello\x0d\n0\x0d\nAuthorization: Bearer token\x0d\n\x0d\n", .exact r400),
    ("forbidden-field policy: cache-control in trailer", "5\x0d\nhello\x0d\n0\x0d\nCache-Control: no-cache\x0d\n\x0d\n", .exact r400),
    ("forbidden-field policy: te in trailer", "5\x0d\nhello\x0d\n0\x0d\nTE: trailers\x0d\n\x0d\n", .exact r400),
    ("Forbidden trailer field names are rejected regardless of case.", "5\x0d\nhello\x0d\n0\x0d\nCONTENT-LENGTH: 0\x0d\n\x0d\n", .exact r400),
    ("a forbidden field before an allowed one", "5\x0d\nhello\x0d\n0\x0d\nContent-Length: 0\x0d\nChecksum: abc\x0d\n\x0d\n", .exact r400)
  ] fun (_, chunked, want) => expectServer ("POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n" ++ chunked) echoHandler want trailerConfig


-- RFC 9112 §7.1.2, §2.2: a malformed trailer section must not let the next bytes become a request.
#eval checkCases "Trailer smuggling: the follower is never served" #[
    ("a trailer line without a colon", "0\x0d\nBadTrailer\x0d\n\x0d\n"),
    ("a trailer section ended by a bare LF", "0\x0d\n\n"),
    ("a trailer line ended by a bare LF", "0\x0d\nX-T: v\n\x0d\n"),
    ("a bare CR in a trailer", "0\x0d\nX-T: v\x0dw\x0d\n\x0d\n")
  ] fun (_, tail) => do
    let (r, seen) ← serveRecording ("POST /first HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\n\x0d\n3\x0d\nabc\x0d\n" ++
      tail ++ "GET /smuggled HTTP/1.1\x0d\nHost: example.com\x0d\n\x0d\n") (config := trailerConfig)
    ensure (!seen.any (·.target == "/smuggled")) s!"/smuggled was served: {repr seen}"
    (Want.all [.status "HTTP/1.1 400", .responses 1]).check r

/-! ## Truncated bodies (RFC 9112 §6.3, §7.1, §8) -/

#eval checkCases "Truncated bodies: machine" #[
    ("§6.3: noMoreInput mid fixed-length body → connectionClosed", MachineTester.receiving "§6.3: noMoreInput mid fixed-length body → connectionClosed"
      |>.feed (mkPostHead "/" 10 ++ "hello")
      |>.step |>.assertHasEndHeaders |>.noMoreInput
      |>.drainBody |>.assertFailedWith .connectionClosed |>.run),
    ("§7.1: noMoreInput mid chunked body → connectionClosed", MachineTester.receiving "§7.1: noMoreInput mid chunked body → connectionClosed"
      |>.feed (mkChunkedPost "/" ++ "5\r\n")  -- chunk size line but no chunk payload
      |>.step |>.assertHasEndHeaders |>.noMoreInput
      |>.pullBody   -- tries to read 5-byte chunk data, hits EOF → connectionClosed
      |>.assertFailedWith .connectionClosed |>.run)
  ] (·.2)

#eval checkCases "Incomplete trailer section at EOF" #[
    -- The client closes both directions: the server returns (inside the guard) and writes nothing.
    ("trailer line without the final CRLF, then a full close", do
      let (client, server) ← Internal.Mock.new
      let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n3\x0d\nabc\x0d\n0\x0d\nX-Trailer: value\x0d\n".toUTF8
      let response ← Async.block do
        client.send raw
        client.close
        Server.serveConnection server echoHandler { lingeringTimeout := 1000, generateDate := false } |>.run
        return (← client.recv?).getD .empty
      ensure (response.size == 0) s!"expected no response bytes, got {response.size}"),
    -- Only the client's sending side closes: the truncated message is answered with 400.
    ("trailer line without the final CRLF, then a half close", checkHandler
      "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n3\x0d\nabc\x0d\n0\x0d\nX-Trailer: value\x0d\n" echoHandler (.exact r400) (closeInput := true))
  ] (·.2)


-- RFC 9112 §8: a chunked message without its last chunk and trailer section is incomplete. The
-- prefix ending `0\r\n` waits for policy P2.
#eval checkCases "Every proper prefix of a chunked body, then EOF" #[
    ("prefixes", do
      let head := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n"
      let body := "5;e=v\x0d\nhello\x0d\n0\x0d\nX-T: v\x0d\n\x0d\n"
      let p2 := "5;e=v\x0d\nhello\x0d\n0\x0d\n".length
      for n in [0:body.length] do
        if n == p2 then continue
        try checkHandler (head ++ String.ofList (body.toList.take n)) echoHandler (.exact r400) trailerConfig (closeInput := true)
        catch e => throw <| IO.userError s!"prefix of {n} body bytes: {e}")
  ] (·.2)

/-! ## Smuggling vectors (RFC 9112 §6.1, §6.3) -/

#eval checkCases "Smuggling vectors: machine" #[
    ("§6.3: Transfer-Encoding on two field lines with Content-Length → badMessage",
      MachineTester.receiving "§6.3: Transfer-Encoding on two field lines with Content-Length → badMessage"
      |>.feed ("POST / HTTP/1.1\r\nHost: example.com\r\nTransfer-Encoding: gzip\r\n" ++
        "Transfer-Encoding: chunked\r\nContent-Length: 3\r\n\r\n")
      |>.step |>.assertFailedWith .badMessage |>.run),
    ("§6.3: CL + TE mixed → badMessage (request-smuggling prevention)",
      MachineTester.receiving "§6.3: CL + TE mixed → badMessage (request-smuggling prevention)"
      |>.feed "POST / HTTP/1.1\r\nHost: example.com\r\nContent-Length: 5\r\nTransfer-Encoding: chunked\r\n\r\n"
      |>.step |>.assertFailedWith .badMessage |>.run)
  ] (·.2)

-- TE + CL → request smuggling prevention.
#eval checkCases "TE + Content-Length → 400: server" #[
    ("TE + Content-Length → 400", "5", okHandler),
    ("TE + Content-Length: 0", "0", echoHandler), ("TE + Content-Length: 1", "1", echoHandler),
    ("TE + Content-Length: 5", "5", echoHandler), ("TE + Content-Length: 128", "128", echoHandler)
  ] fun (_, cl, handler) =>
    expectServer s!"POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nContent-Length: {cl}\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n"
      handler (.exact r400)

#eval checkCases "Smuggling vectors: exact answers" #[
    ("Request smuggling: CL.TE",
      "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 6\x0d\nTransfer-Encoding: chunked\x0d\n\x0d\n0\x0d\n\x0d\nX"),
    ("Request smuggling: TE.CL",
      "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nContent-Length: 3\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n"),
    -- RFC 9112 §5.1: no whitespace is allowed between a field name and the colon.
    ("Transfer-Encoding : chunked",
      "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding : chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n")
  ] fun (_, raw) => checkHandler raw okHandler (.exact r400) (closeInput := true)
