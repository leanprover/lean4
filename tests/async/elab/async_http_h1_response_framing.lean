module

import Std.Http.Test.Helpers
import Std.Http.Test.Machine

/-!
# HTTP/1.1 response framing

What a server writes as a response: `Date` and the responses it writes itself, HEAD, 204, 205 and 304,
interim responses, HTTP/1.0 peers, handler framing that contradicts the body, transfer codings from
the handler, the chunked writer, and CONNECT. Machine tables first, then `serveConnection` tables.
RFC 9110 §6.6.1, §9.3.2, §9.3.6, §15.2–§15.6; RFC 9112 §6, §7.1. Regressions: #15469, #16282,
#16362.
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

private def ok200Head : String :=
  "HTTP/1.1 200 OK\x0d\nContent-Type: text/plain; charset=utf-8\x0d\nServer: LeanHTTP/1.1\x0d\nConnection: close\x0d\nContent-Length: 2\x0d\n\x0d\n"

/-- A server machine that has read `request`. -/
private def server (request : String) : Machine .receiving :=
  (({ config := {} } : Machine .receiving).feed request.toUTF8).step.1

private def headers (fields : List (Header.Name × String)) : Headers :=
  fields.foldl (fun hs (name, value) => hs.insert name (Header.Value.ofString! value)) .empty

private def get : String := "GET / HTTP/1.1\r\nHost: a\r\n\r\n"

private def abc : Array Chunk := #[Chunk.ofByteArray "abc".toUTF8]

/-- Runs `machine` to a halt and checks that it answered 500 with its explanation, not the body. -/
private def expect500 (name : String) (machine : Machine .receiving) : IO Unit := do
  let some (out, events) := runToHalt (machine.sendData abc |>.userClosedBody)
    | throw <| IO.userError s!"[{name}] the server never halted"
  unless out == "HTTP/1.1 500 Internal Server Error\r\nContent-Type: text/plain; charset=utf-8\r\n" ++
      "Connection: close\r\nContent-Length: 22\r\n\r\nInternal Server Error\n" do
    throw <| IO.userError s!"[{name}] expected a 500 with its explanation only, got:\n{out.quote}"
  unless events.any (· matches .failed (.other _)) do
    throw <| IO.userError s!"[{name}] no framing failure reported: {repr events}"

/-- Runs `machine` to a halt and returns its output, failing on a reported failure. -/
private def expectOk (name : String) (machine : Machine .receiving) : IO String := do
  let some (out, events) := runToHalt machine
    | throw <| IO.userError s!"[{name}] the server never halted"
  if events.any (· matches .failed _) then
    throw <| IO.userError s!"[{name}] unexpected failure: {repr events}\n{out.quote}"
  return out

private def connectRequest : String :=
  "CONNECT example.com:443 HTTP/1.1\x0d\nHost: example.com:443\x0d\n\x0d\n"

/-- Bytes a client sends through the tunnel it believes is open. -/
private def tunnelBytes : String :=
  "GET /admin HTTP/1.1\x0d\nHost: a\x0d\nConnection: close\x0d\n\x0d\n"

private def handledHandler : TestHandler := fun req =>
  Response.ok |>.text s!"handled {req.line.method} {req.line.uri}"

private def codedHandler : TestHandler := fun _ =>
  Response.ok
    |>.header! "Transfer-Encoding" "gzip, chunked"
    |>.stream fun out => out.send (Chunk.ofByteArray "GZIPPED".toUTF8)

private def date : Header.Value := .mk "Mon, 01 Jan 2024 00:00:00 GMT"

private def withDate (t : MachineTester .receiving) : MachineTester .receiving :=
  { t with machine := { t.machine with date := some date } }

/-! ## Server-written responses and Date (RFC 9110 §6.6.1, §15.5, §15.6) -/

#eval checkCases "Server-written responses and Date: machine" #[
    ("§6.6.1: the machine's date goes into a response without Date", do
      MachineTester.receiving "§6.6.1: the machine's date goes into a response without Date"
        |> withDate
        |>.feed (mkGet "/") |>.step
        |>.send { status := .ok } |>.setKnownSize (.fixed 0) |>.userClosedBody |>.step
        |>.assertOutputStartsWith "HTTP/1.1 200 OK\r\nDate: Mon, 01 Jan 2024 00:00:00 GMT\r\nContent-Length: 0\r\n"
            "expected the machine's Date after the handler's fields" |>.run),
    ("§6.6.1: the handler's own Date is kept and not duplicated", do
      MachineTester.receiving "§6.6.1: the handler's own Date is kept and not duplicated"
        |> withDate
        |>.feed (mkGet "/") |>.step
        |>.send { status := .ok, headers := Headers.empty.insert! "Date" "Tue, 02 Jan 2024 00:00:00 GMT" }
        |>.setKnownSize (.fixed 0) |>.userClosedBody |>.step
        |>.assertOutputContains "Date: Tue, 02 Jan 2024 00:00:00 GMT\r\n" "expected the handler's Date"
        |>.assertOutputNotContains "Mon, 01 Jan 2024" "the machine's Date must not be added too" |>.run),
    ("§6.6.1: a 400 the machine writes itself carries Date", do
      MachineTester.receiving "§6.6.1: a 400 the machine writes itself carries Date"
        |> withDate
        |>.feed "GET / HTTP/1.1\r\n\r\n" |>.step |>.step
        |>.assertOutputStartsWith
            "HTTP/1.1 400 Bad Request\r\nContent-Type: text/plain; charset=utf-8\r\nDate: Mon, 01 Jan 2024 00:00:00 GMT\r\n"
            "expected Date on the machine's 400" |>.run),
    ("§6.6.1: a 408 from closeWithError carries Date", do
      MachineTester.receiving "§6.6.1: a 408 from closeWithError carries Date"
        |> withDate
        |>.feed (mkPostHead "/" 5) |>.step
        |>.closeWithError .requestTimeout |>.step
        |>.assertOutputStartsWith
            "HTTP/1.1 408 Request Timeout\r\nContent-Type: text/plain; charset=utf-8\r\nDate: Mon, 01 Jan 2024 00:00:00 GMT\r\n"
            "expected Date on the 408" |>.run),
    ("§6.6.1: the 500 for a rejected head carries Date and an explanation", do
      MachineTester.receiving "§6.6.1: the 500 for a rejected head carries Date and an explanation"
        |> withDate
        |>.feed (mkGet "/") |>.step
        |>.setKnownSize (.fixed 0)
        |>.send { status := .ok, headers := Headers.empty.insert! "Content-Length" "4" } |>.step
        |>.assertOutputStartsWith
            ("HTTP/1.1 500 Internal Server Error\r\nContent-Type: text/plain; charset=utf-8\r\n" ++
              "Date: Mon, 01 Jan 2024 00:00:00 GMT\r\nConnection: close\r\nContent-Length: 22\r\n\r\n" ++
              "Internal Server Error\n")
            "expected Date and the explanation on the 500" |>.run),
    ("§6.6.1: without a date the machine adds no Date", do
      MachineTester.receiving "§6.6.1: without a date the machine adds no Date"
        |>.feed "GET / HTTP/1.1\r\n\r\n" |>.step |>.step
        |>.assertOutputNotContains "Date" "no Date without a date value" |>.run),
    ("§15.5: a 400 the machine writes explains itself", do
      -- §15.5, §15.6: except for a response to HEAD, a 4xx or 5xx response should explain the error
      MachineTester.receiving "§15.5: a 400 the machine writes explains itself"
        |>.feed "GET / HTTP/1.1\r\n\r\n" |>.step |>.step
        |>.assertOutputStartsWith
            ("HTTP/1.1 400 Bad Request\r\nContent-Type: text/plain; charset=utf-8\r\n" ++
              "Connection: close\r\nContent-Length: 12\r\n\r\nBad Request\n")
            "expected a text/plain explanation" |>.run),
    ("§15.6.6: a 505 names the supported versions", do
      -- §15.6.6: a 505 says which versions the server supports
      MachineTester.receiving "§15.6.6: a 505 names the supported versions"
        |>.feed "GET / HTTP/2.0\r\nHost: example.com\r\n\r\n" |>.step |>.step
        |>.assertOutputStartsWith "HTTP/1.1 505 HTTP Version Not Supported\r\n" "expected 505"
        |>.assertOutputContains "\r\n\r\nHTTP Version Not Supported: this server supports HTTP/1.0 and HTTP/1.1\n"
            "expected the supported versions" |>.run),
    ("§9.3.2: a 400 to HEAD keeps Content-Length and omits the content", do
      -- §9.3.2: a response to HEAD has no content, but keeps the Content-Length GET would have
      MachineTester.receiving "§9.3.2: a 400 to HEAD keeps Content-Length and omits the content"
        |>.feed "HEAD / HTTP/1.1\r\n\r\n" |>.step |>.step
        |>.assertOutputStartsWith "HTTP/1.1 400 Bad Request\r\n" "expected 400"
        |>.assertOutputContains "Content-Length: 12\r\n\r\n" "expected the content's length"
        |>.assertOutputNotContains "\r\n\r\nBad Request" "a HEAD response carries no content" |>.run),
    ("§15.5: a 408 from closeWithError explains itself", do
      MachineTester.receiving "§15.5: a 408 from closeWithError explains itself"
        |>.feed (mkPostHead "/" 5) |>.step
        |>.closeWithError .requestTimeout |>.step
        |>.assertOutputStartsWith "HTTP/1.1 408 Request Timeout\r\n" "expected 408"
        |>.assertOutputContains "Connection: close\r\n" "expected Connection: close"
        |>.assertOutputContains "Content-Length: 16\r\n\r\nRequest Timeout\n" "expected an explanation"
        |>.assertNotKeepAlive |>.run)
  ] (·.2)

#eval checkCases "Server-written responses and Date: async_http_expect.lean" #[
    ("generateDate: true adds Date header",
      do
        check "generateDate: true adds Date header"
          (raw := mkGetClose "/date")
          (handler := fun _ => Response.ok |>.text "hello")
          (config := { defaultConfig with generateDate := true })
          (expect := fun r =>
            assertStatus r "HTTP/1.1 200" *>
            assertContains r "Date: " *>
            assertContains r " GMT\x0d\n")),
    ("generateDate: false omits Date header",
      do
        check "generateDate: false omits Date header"
          (raw := mkGetClose "/no-date")
          (handler := fun _ => Response.ok |>.text "hello")
          (config := { defaultConfig with generateDate := false })
          (expect := fun r =>
            assertStatus r "HTTP/1.1 200" *>
            assertAbsent r "Date: ")),
    ("user-supplied Date header preserved and not duplicated",
      do
        check "user-supplied Date header preserved and not duplicated"
          (raw := mkGetClose "/custom-date")
          (handler := fun _ =>
            Response.ok
              |>.header! "Date" "Mon, 01 Jan 2024 00:00:00 GMT"
              |>.text "hello")
          (config := { defaultConfig with generateDate := true })
          (expect := fun r => do
            assertContains r "Date: Mon, 01 Jan 2024 00:00:00 GMT"
            let text := String.fromUTF8! r
            let count := (text.splitOn "Date: ").length - 1
            unless count == 1 do
              throw <| IO.userError s!"expected 1 Date header, got {count}:\n{text.quote}")),
    ("generateDate: true adds Date to a 400 the server writes itself",
      do
        -- RFC 9110 §6.6.1: an origin server MUST generate a Date field in all 2xx, 3xx and 4xx responses,
        -- including those the server writes itself
        check "generateDate: true adds Date to a 400 the server writes itself"
          (raw := "GET / HTTP/1.1\x0d\nConnection: close\x0d\n\x0d\n")
          (handler := okHandler)
          (config := { defaultConfig with generateDate := true })
          (expect := fun r =>
            assertStatus r "HTTP/1.1 400" *>
            assertContains r "\x0d\nDate: " *>
            assertContains r " GMT\x0d\nServer: LeanHTTP/1.1\x0d\n")),
    ("generateDate: true adds Date to a 431 the server writes itself",
      do
        check "generateDate: true adds Date to a 431 the server writes itself"
          (raw := "GET / HTTP/1.1\x0d\nHost: example.com\x0d\nA: 1\x0d\nB: 2\x0d\nC: 3\x0d\n\x0d\n")
          (handler := okHandler)
          (config := { defaultConfig with generateDate := true, maxHeaders := 2 })
          (expect := fun r =>
            assertStatus r "HTTP/1.1 431" *>
            assertContains r "\x0d\nDate: ")),
    ("generateDate: true adds Date to the 500 for a handler head with a wrong Content-Length",
      do
        check "generateDate: true adds Date to the 500 for a handler head with a wrong Content-Length"
          (raw := "GET / HTTP/1.1\x0d\nHost: example.com\x0d\n\x0d\n")
          (handler := fun _ => Response.ok |>.header! "Content-Length" "1234" |>.text "")
          (config := { defaultConfig with generateDate := true })
          (expect := fun r =>
            assertStatus r "HTTP/1.1 500" *>
            assertContains r "\x0d\nDate: " *>
            assertContains r "\x0d\n\x0d\nInternal Server Error\n")),
    ("generateDate: false adds no Date to a 400 the server writes itself",
      do
        check "generateDate: false adds no Date to a 400 the server writes itself"
          (raw := "GET / HTTP/1.1\x0d\nConnection: close\x0d\n\x0d\n")
          (handler := okHandler)
          (config := { defaultConfig with generateDate := false })
          (expect := (assertExact · r400)))
  ] (·.2)

#eval checkCases "Server-written responses and Date: async_http_h1_framing_mismatch.lean" #[
    ("empty body with Content-Length: 1234",
      do
        checkTimed "empty body with Content-Length: 1234"
          (raw := get)
          (handler := fun _ => Response.ok |>.header! "Content-Length" "1234" |>.text "")
          (expect := (assertStatus · "HTTP/1.1 500 Internal Server Error")))
  ] (·.2)


/-- The number of field lines named `name` in the first head of `text`. -/
private def fieldCount (text name : String) : Nat :=
  ((text.splitOn "\x0d\n\x0d\n").headD "").splitOn "\x0d\n" |>.filter (·.toLower.startsWith (name.toLower ++ ":")) |>.length

private def ownFields : TestHandler := fun _ =>
  Response.ok |>.header! "Server" "Mine/1.0" |>.header! "Date" "Mon, 01 Jan 2024 00:00:00 GMT"
    |>.header! "Content-Type" "text/html" |>.text "x"

-- RFC 9110 §6.6.1, §10.2.4, §8.3: a response has at most one `Date`, `Server` and `Content-Type`.
#eval checkCases "One Server, one Date, one Content-Type" #[
    ("server defaults", (okHandler : TestHandler)), ("set by the handler", ownFields)
  ] fun (_, handler) => do
    let r ← serveRaw "GET / HTTP/1.1\x0d\nHost: a\x0d\nConnection: close\x0d\n\x0d\n" handler
      { testConfig with generateDate := true }
    let text := String.fromUTF8! r
    for name in ["Server", "Date", "Content-Type"] do
      ensure (fieldCount text name == 1) s!"{fieldCount text name} {name} fields:\n{text.quote}"

/-! ## HEAD (RFC 9110 §9.3.2) -/

#eval checkCases "HEAD: machine" #[
    ("RFC 9110 §9.3.2: HEAD response — body bytes suppressed, Content-Length preserved", do
      -- body bytes suppressed; Content-Length metadata still emitted so client knows size
      let body := "hello".toUTF8
      MachineTester.receiving "RFC 9110 §9.3.2: HEAD response — body bytes suppressed, Content-Length preserved"
        |>.feed "HEAD / HTTP/1.1\r\nHost: example.com\r\n\r\n"
        |>.step |>.assertIsWaitingMessage
        |>.send { status := .ok, headers := Headers.empty.insert! "Content-Length" "5" }
        |>.sendBytes body |>.userClosedBody |>.step |>.step
        |>.assertOutputContains "HTTP/1.1 200" "expected 200 OK status line"
        |>.assertOutputContains "Content-Length: 5" "expected Content-Length metadata preserved"
        |>.assertOutputNotContains "hello" "HEAD response must not contain body bytes on the wire"
        |>.run),
    ("§9.3.2: HEAD response of unknown length has no Content-Length: 0", do
      -- RFC 9110 §9.3.2, §8.6: with no known length a HEAD response has GET's framing; a
      -- `Content-Length: 0` would claim the GET response is empty
      MachineTester.receiving "§9.3.2: HEAD response of unknown length has no Content-Length: 0"
        |>.feed ("HEAD / HTTP/1.1\r\nHost: example.com\r\n\r\n" ++ mkGet "/next")
        |>.step |>.assertIsWaitingMessage
        |>.send { status := .ok } |>.userClosedBody |>.step
        |>.assertOutputNotContains "Content-Length" "unknown length must not be sent as Content-Length: 0"
        |>.assertOutputContains "Transfer-Encoding: chunked\r\n" "expected the framing GET would have"
        |>.assertOutputNotContains "0\r\n\r\n" "a HEAD response carries no body, not even a last chunk"
        |>.assertHasNext |>.run)
  ] (·.2)

#eval checkCases "HEAD: async_http_h1_framing_mismatch.lean" #[
    ("HEAD keeps the handler's Content-Length",
      do
        let head := "HEAD / HTTP/1.1\r\nHost: a\r\nConnection: close\r\n\r\n"
        for size in [Body.Length.chunked, .fixed 0] do
          let out ← expectOk s!"HEAD, {repr size}" <| server head
            |>.setKnownSize size
            |>.send { status := .ok, headers := headers [(Header.Name.contentLength, "1234")] }
          unless out.startsWith "HTTP/1.1 200 OK\r\n" && out.contains "Content-Length: 1234\r\n" &&
              !out.contains "Transfer-Encoding" do
            throw <| IO.userError s!"HEAD, {repr size}: expected Content-Length: 1234, got\n{out.quote}"),
    ("HEAD with a streamed body and Content-Length: 1234",
      do
        checkTimed "HEAD with a streamed body and Content-Length: 1234"
          (raw := "HEAD / HTTP/1.1\r\nHost: a\r\nConnection: close\r\n\r\n")
          (handler := fun _ => Response.ok |>.header! "Content-Length" "1234"
            |>.stream fun s => s.send (Chunk.ofByteArray "abc".toUTF8))
          (expect := fun r => do
            assertStatus r "HTTP/1.1 200 OK"
            assertContains r "Content-Length: 1234\r\n"
            assertAbsent r "abc"))
  ] (·.2)

#eval checkCases "HEAD: async_http_response_framing.lean" #[
    ("HEAD omits body bytes, preserves headers",
      do
        check "HEAD omits body bytes, preserves headers"
          (raw := "HEAD / HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")
          (handler := okHandler)
          (expect := fun r => assertExact r ok200Head)),
    ("GET and HEAD produce identical header sections",
      do
        check "GET and HEAD produce identical header sections"
          (raw := "GET /frame HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")
          (handler := fun _ => Response.ok |>.text "hello")
          (expect := fun getResp => do
            -- Run HEAD against the same handler
            let (client2, server2) ← Mock.new
            let headResp ← Async.block do
              client2.send "HEAD /frame HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
              Std.Http.Server.serveConnection server2 (show TestHandler from fun _ => Response.ok |>.text "hello") defaultConfig |>.run
              return (← client2.recv?).getD .empty

            let getHeaders := (String.fromUTF8! getResp).splitOn "\x0d\n\x0d\n" |>.headD ""
            let headHeaders := (String.fromUTF8! headResp).splitOn "\x0d\n\x0d\n" |>.headD ""
            unless getHeaders == headHeaders do
              throw <| IO.userError s!"headers differ:\nGET: {getHeaders.quote}\nHEAD: {headHeaders.quote}"
            assertContains getResp "hello" *>
            assertAbsent headResp "hello"))
  ] (·.2)


private def sized (n : Nat) : TestHandler := fun _ =>
  Response.ok |>.text (String.ofList (List.replicate n 'b'))

-- RFC 9110 §9.3.2: a HEAD response carries the GET's framing fields and no content.
#eval checkCases "HEAD, then a pipelined GET" #[
    ("10 bytes", 10), ("4 KiB", 4096)
  ] fun (_, n) => do
    let r ← serveRaw "HEAD / HTTP/1.1\x0d\nHost: a\x0d\n\x0d\nGET / HTTP/1.1\x0d\nHost: a\x0d\nConnection: close\x0d\n\x0d\n" (sized n)
    let text := String.fromUTF8! r
    let some [h1, h2, body] := some (text.splitOn "\x0d\n\x0d\n")
      | throw <| IO.userError s!"expected two heads and one body:\n{text.quote}"
    ensure (h1.startsWith "HTTP/1.1 200" && h1.contains s!"Content-Length: {n}" && !h1.contains "Transfer-Encoding")
      s!"HEAD response head:\n{h1.quote}"
    ensure (h2.startsWith "HTTP/1.1 200" && h2.contains s!"Content-Length: {n}") s!"GET response head:\n{h2.quote}"
    ensure (body == String.ofList (List.replicate n 'b')) s!"GET body of {body.length} bytes"

private def streamed : TestHandler := fun _ =>
  Response.ok |>.stream fun s => s.send (Chunk.ofByteArray "abc".toUTF8)

private def bothFraming : TestHandler := fun _ =>
  Response.ok |>.header! "Content-Length" "3" |>.header! "Transfer-Encoding" "chunked" |>.text "abc"

#eval checkCases "HEAD with an unknown length" #[
    ("HTTP/1.0, streamed: Connection: close and no TE", "HEAD / HTTP/1.0\x0d\n\x0d\n", streamed,
      Want.all [.status "HTTP/1.1 200", .contains "Connection: close\x0d\n", .absent "Transfer-Encoding", .absent "abc"]),
    ("CL and TE from the handler: no 500", "HEAD / HTTP/1.1\x0d\nHost: a\x0d\nConnection: close\x0d\n\x0d\n", bothFraming,
      .all [.status "HTTP/1.1 200", .absent "abc"])
  ] fun (_, raw, handler, want) => checkHandler raw handler want (closeInput := true)

/-! ## 204, 205 and 304 (RFC 9110 §15.3.5, §15.3.6, §15.4.5) -/

#eval checkCases "204, 205 and 304: machine" #[
    ("§15.3.6: 205 drops the handler's content and sends Content-Length: 0", do
      -- RFC 9110 §15.3.6: a server must not generate content in a 205 response; it sends
      -- `Content-Length: 0` whatever length or framing the handler gave
      MachineTester.receiving "§15.3.6: 205 drops the handler's content and sends Content-Length: 0"
        |>.feed (mkGet "/") |>.step |>.assertIsWaitingMessage
        |>.send { status := .resetContent } |>.sendBytes "body".toUTF8 |>.userClosedBody |>.step
        |>.assertOutputStartsWith "HTTP/1.1 205 Reset Content\r\nContent-Length: 0\r\n\r\n"
            "expected a 205 head with Content-Length: 0"
        |>.assertOutputNotContains "body" "a 205 response carries no content"
        |>.assertNoError |>.assertKeepAlive |>.run),
    ("§15.3.6: 205 with the handler's Content-Length: 4 still sends Content-Length: 0", do
      MachineTester.receiving "§15.3.6: 205 with the handler's Content-Length: 4 still sends Content-Length: 0"
        |>.feed (mkGet "/") |>.step |>.assertIsWaitingMessage
        |>.send { status := .resetContent, headers := Headers.empty.insert! "Content-Length" "4" }
        |>.sendBytes "body".toUTF8 |>.userClosedBody |>.step
        |>.assertOutputContains "Content-Length: 0\r\n\r\n" "expected Content-Length: 0"
        |>.assertOutputNotContains "Content-Length: 4" "the handler's length must not be advertised"
        |>.assertOutputNotContains "body" "a 205 response carries no content"
        |>.assertNoError |>.run),
    ("§15.3.6: 205 of unknown length is not chunked", do
      MachineTester.receiving "§15.3.6: 205 of unknown length is not chunked"
        |>.feed (mkGet "/") |>.step |>.assertIsWaitingMessage
        |>.send { status := .resetContent } |>.setKnownSize .chunked |>.sendBytes "body".toUTF8
        |>.userClosedBody |>.step
        |>.assertOutputContains "Content-Length: 0\r\n\r\n" "expected Content-Length: 0"
        |>.assertOutputNotContains "Transfer-Encoding" "a 205 response is not chunked"
        |>.assertOutputNotContains "body" "a 205 response carries no content" |>.run)
  ] (·.2)

#eval checkCases "204, 205 and 304: async_http_h1_framing_mismatch.lean" #[
    ("204 and 304 drop the handler's framing fields",
      do
        let close := "GET / HTTP/1.1\r\nHost: a\r\nConnection: close\r\n\r\n"
        for status in [Status.noContent, .notModified] do
          let out ← expectOk s!"{status}" <| server close
            |>.setKnownSize (.fixed 0)
            |>.send { status, headers := headers [(Header.Name.contentLength, "9")] }
          unless out.startsWith s!"HTTP/1.1 {status.toCode} " && !out.contains "Content-Length" do
            throw <| IO.userError s!"{status}: expected no framing fields, got\n{out.quote}")
  ] (·.2)

#eval checkCases "204, 205 and 304: async_http_response_framing.lean" #[
    ("Direct machine test: write a 304 head with Content-Length: 5 and verify it is stripped.",
      do
        -- Direct machine test: write a 304 head with Content-Length: 5 and verify it is stripped.
        -- RFC 9110 §8.6 permits Content-Length in 304 as optional metadata, but we strip it to
        -- avoid forwarding a stale or wrong value from a handler that did not intend to advertise
        -- a body size.
        let request := "GET /cache HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
        let machine0 : Protocol.H1.Machine .receiving := { config := {} }
        let (machine1, _) := (machine0.feed request).step
        let headers304 := Headers.empty.insert Header.Name.contentLength (Header.Value.ofString! "5")
        let (_, step304) := (machine1.send ({ status := .notModified, headers := headers304 } : Response.Head)).step
        let text304 := String.fromUTF8! step304.output.toByteArray
        unless text304.contains "HTTP/1.1 304 Not Modified" do
          throw <| IO.userError s!"expected 304 status in output:\n{text304.quote}"
        if text304.contains "Content-Length:" || text304.contains "Transfer-Encoding:" then
          throw <| IO.userError s!"unexpected framing headers in 304:\n{text304.quote}"),
    ("RFC 9110 §15.3.5: 204 No Content strips framing headers",
      do
        let request := "GET /empty HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
        let machine0 : Protocol.H1.Machine .receiving := { config := {} }
        let (machine1, _) := (machine0.feed request).step
        let headers204 := Headers.empty.insert Header.Name.contentLength (Header.Value.ofString! "9")
        let (_, step204) := (machine1.send ({ status := .noContent, headers := headers204 } : Response.Head)).step
        let text204 := String.fromUTF8! step204.output.toByteArray
        unless step204.output.size > 0 do
          throw <| IO.userError "expected serialized response output"
        unless text204.contains "HTTP/1.1 204 No Content" do
          throw <| IO.userError s!"expected 204 status:\n{text204.quote}"
        if text204.contains "Content-Length:" || text204.contains "Transfer-Encoding:" then
          throw <| IO.userError s!"unexpected framing headers in 204:\n{text204.quote}")
  ] (·.2)


private def withLength (status : Status) : TestHandler := fun _ =>
  Response.withStatus status |>.header! "Content-Length" "123" |>.text "stuff"

-- RFC 9110 §8.6, §15.3.5, §15.4.5: 204 and 304 have no content and no framing fields.
#eval checkCases "204 and 304 with a handler's Content-Length and content" #[
    ("204, HTTP/1.1", Status.noContent, "GET / HTTP/1.1\x0d\nHost: a\x0d\nConnection: close\x0d\n\x0d\n"),
    ("204, HTTP/1.0", .noContent, "GET / HTTP/1.0\x0d\n\x0d\n"),
    ("304, HTTP/1.1", .notModified, "GET / HTTP/1.1\x0d\nHost: a\x0d\nConnection: close\x0d\n\x0d\n"),
    ("304, HTTP/1.0", .notModified, "GET / HTTP/1.0\x0d\n\x0d\n")
  ] fun (_, status, raw) => do
    let text := String.fromUTF8! (← serveRaw raw (withLength status) (closeInput := true))
    ensure (text.startsWith s!"HTTP/1.1 {status.toCode}") s!"status:\n{text.quote}"
    ensure (fieldCount text "Content-Length" == 0 && fieldCount text "Transfer-Encoding" == 0) s!"framing fields:\n{text.quote}"
    ensure (fieldCount text "Content-Type" == 1) s!"Content-Type dropped:\n{text.quote}"
    ensure (text.endsWith "\x0d\n\x0d\n" && !text.contains "stuff") s!"content bytes:\n{text.quote}"

/-! ## Interim responses (RFC 9110 §15.2) -/

#eval checkCases "Interim responses: machine" #[
    ("§15.2: 103 Early Hints is not sent to an HTTP/1.0 client", do
      -- RFC 9110 §15.2: a server must not send a 1xx response to an HTTP/1.0 client
      MachineTester.receiving "§15.2: 103 Early Hints is not sent to an HTTP/1.0 client"
        |>.feed (mkGet10 "/") |>.step |>.assertIsWaitingMessage
        |>.send { status := .earlyHints, headers := Headers.empty.insert! "Link" "</a.css>; rel=preload" }
        |>.step |>.assertIsWaitingMessage
        |>.send { status := .ok } |>.setKnownSize (.fixed 0) |>.userClosedBody |>.step
        |>.assertOutputNotContains "103" "a 1xx response must not reach an HTTP/1.0 client"
        |>.assertOutputStartsWith "HTTP/1.1 200" "expected the final response first" |>.run)
  ] (·.2)

#eval checkCases "Interim responses: async_http_response_framing.lean" #[
    ("100 Continue: handler-set Content-Length must be stripped",
      do
        let request := "GET / HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
        let machine0 : Protocol.H1.Machine .receiving := { config := {} }
        let (machine1, _) := (machine0.feed request).step
        -- 100 Continue: handler-set Content-Length must be stripped
        let headers100 := Headers.empty
          |>.insert Header.Name.contentLength (Header.Value.ofString! "5")
        let (machine2, step100) := (machine1.send ({ status := .«continue», headers := headers100 } : Response.Head)).step
        let text100 := String.fromUTF8! step100.output.toByteArray
        unless text100.contains "HTTP/1.1 100 Continue" do
          throw <| IO.userError s!"expected 100 status in output:\n{text100.quote}"
        if text100.contains "Content-Length:" then
          throw <| IO.userError s!"Content-Length must not appear in 1xx output:\n{text100.quote}"

        -- 103 Early Hints: both Content-Length and Transfer-Encoding must be stripped
        let headers103 := Headers.empty
          |>.insert Header.Name.contentLength (Header.Value.ofString! "42")
          |>.insert Header.Name.transferEncoding (Header.Value.ofString! "chunked")
        let (machine3, step103) := (machine2.send ({ status := .earlyHints, headers := headers103 } : Response.Head)).step
        let text103 := String.fromUTF8! step103.output.toByteArray
        unless text103.contains "HTTP/1.1 103 Early Hints" do
          throw <| IO.userError s!"expected 103 status in output:\n{text103.quote}"
        if text103.contains "Content-Length:" || text103.contains "Transfer-Encoding:" then
          throw <| IO.userError s!"framing headers must not appear in 1xx output:\n{text103.quote}"

        -- Machine must remain in waitingHeaders after sending 1xx (interim does not advance writer)
        unless machine3.writer.state == .waitingHeaders do
          throw <| IO.userError s!"writer must stay in waitingHeaders after 1xx, got: {repr machine3.writer.state}"

        -- Final 200 OK still works after chained 1xx responses
        let headers200 := Headers.empty
          |>.insert Header.Name.contentLength (Header.Value.ofString! "0")
        let (_, step200) := (machine3.send ({ status := .ok, headers := headers200 } : Response.Head)).step
        let text200 := String.fromUTF8! step200.output.toByteArray
        unless text200.contains "HTTP/1.1 200 OK" do
          throw <| IO.userError s!"expected 200 after 1xx chain:\n{text200.quote}"
        unless text200.contains "Content-Length: 0" do
          throw <| IO.userError s!"Content-Length must be preserved in final response:\n{text200.quote}")
  ] (·.2)


private structure Counting where
  failures : IO.Ref Nat
  seen : IO.Ref (Array String)
  respond : TestHandler

private instance : Server.Handler Counting where
  onRequest self req := do
    self.seen.modify (·.push (toString req.line.uri))
    self.respond req
  onFailure self _ := self.failures.modify (· + 1)

/-- Serves `raw`, then EOF; returns the bytes written, the targets served and the `onFailure` count. -/
private def serveCounting (raw : String) (respond : TestHandler) : IO (String × Array String × Nat) := do
  let failures ← IO.mkRef 0
  let seen ← IO.mkRef #[]
  let r ← serveRaw raw ({ failures, seen, respond } : Counting) (closeInput := true)
  return (String.fromUTF8! r, ← seen.get, ← failures.get)

-- RFC 9110 §15.2: a 1xx is interim; a handler cannot end the exchange with one.
#eval checkCases "A 1xx as the handler's final response" #[
    ("100", Status.«continue», "GET / HTTP/1.1\x0d\nHost: a\x0d\n\x0d\n"),
    ("102", .processing, "GET / HTTP/1.1\x0d\nHost: a\x0d\n\x0d\n"),
    ("103", .earlyHints, "GET / HTTP/1.1\x0d\nHost: a\x0d\n\x0d\n"),
    ("101 to a request without Upgrade", .switchingProtocols, "GET / HTTP/1.1\x0d\nHost: a\x0d\n\x0d\n"),
    ("103 to HTTP/1.0", .earlyHints, "GET / HTTP/1.0\x0d\n\x0d\n")
  ] fun (_, status, raw) => do
    let (text, _, failures) ← serveCounting raw fun _ => Response.withStatus status |>.text ""
    ensure (text.startsWith "HTTP/1.1 500") s!"expected a 500 first:\n{text.quote}"
    ensure (failures > 0) "onFailure was not called"

/-! ## HTTP/1.0 peers (RFC 9112 §6.1, §9.3) -/

#eval checkCases "HTTP/1.0 peers: machine" #[
    ("§6.2: HTTP/1.0 request → HTTP/1.1 status line, connection-close framing", do
      -- RFC 9110 §6.2: a server sends the highest version it conforms to whose major version is at most
      -- the request's, so an HTTP/1.0 request gets an HTTP/1.1 status line with HTTP/1.0 framing
      MachineTester.receiving "§6.2: HTTP/1.0 request → HTTP/1.1 status line, connection-close framing"
        |>.feed (mkGet10 "/") |>.step
        |>.send { status := .ok } |>.sendBytes "hello".toUTF8 |>.userClosedBody
        |>.step |>.step
        |>.assertOutputStartsWith "HTTP/1.1 200 OK\r\n" "expected an HTTP/1.1 status line"
        |>.assertOutputContains "Connection: close\r\n" "an HTTP/1.0 connection without keep-alive closes"
        |>.assertOutputNotContains "Transfer-Encoding" "HTTP/1.0 has no chunked framing" |>.run),
    ("§6.3: HTTP/1.0 HEAD of unknown length keeps the connection alive", do
      -- RFC 9112 §6.3: a HEAD response ends at its header block, so a length the server does not know
      -- does not cost an HTTP/1.0 client its keep-alive connection
      MachineTester.receiving "§6.3: HTTP/1.0 HEAD of unknown length keeps the connection alive"
        |>.feed ("HEAD / HTTP/1.0\r\nConnection: keep-alive\r\n\r\n" ++
          "GET /second HTTP/1.0\r\nConnection: keep-alive\r\n\r\n")
        |>.step |>.assertIsWaitingMessage
        |>.send { status := .ok } |>.userClosedBody |>.step
        |>.assertOutputContains "Connection: keep-alive\r\n" "expected the HTTP/1.0 keep-alive echo"
        |>.assertOutputNotContains "Content-Length" "unknown length must not be sent as Content-Length: 0"
        |>.assertOutputNotContains "close" "a HEAD response has no body to delimit by closing"
        |>.assertHasNext
        |>.step |>.assertHasEndHeaders |>.assertKeepAlive |>.run)
  ] (·.2)

#eval checkCases "HTTP/1.0 peers: async_http_h1_v10_framing.lean" #[
    ("HTTP/1.0 GET",
      do
        check "HTTP/1.0 GET" "GET / HTTP/1.0\x0d\nHost: a\x0d\n\x0d\n" codedHandler fun r => do
          assertStatus r "HTTP/1.1 500"
          assertAbsent r "GZIPPED"
        -- Control: an HTTP/1.1 client gets the coding and the coded bytes.
        check "HTTP/1.1 GET" (mkGetClose "/") codedHandler fun r => do
          assertStatus r "HTTP/1.1 200"
          assertContains r "Transfer-Encoding: gzip, chunked"
          assertContains r "GZIPPED")
  ] (·.2)

#eval checkCases "HTTP/1.0 peers: async_http_response_framing.lean" #[
    ("RFC 9112 §6.1: HTTP/1.0 connection-close — headers",
      do
        let request10 := "GET / HTTP/1.0\x0d\nHost: example.com\x0d\n\x0d\n".toUTF8
        let machine0 : Protocol.H1.Machine .receiving := { config := {} }
        let (machine1, _) := (machine0.feed request10).step
        let (_, stepA) := (machine1.send ({ status := .ok, headers := .empty } : Response.Head)).step
        let textA := String.fromUTF8! stepA.output.toByteArray
        unless textA.contains "200 OK" do
          throw <| IO.userError s!"expected 200 status line:\n{textA.quote}"
        if textA.contains "Transfer-Encoding:" then
          throw <| IO.userError s!"Transfer-Encoding must not appear in HTTP/1.0 response:\n{textA.quote}"
        if textA.contains "Content-Length:" then
          throw <| IO.userError s!"Content-Length must not appear when body length is unknown:\n{textA.quote}"),
    ("Non-empty body: raw bytes must appear in output without chunk framing.",
      do
        let request10 := "GET / HTTP/1.0\x0d\nHost: example.com\x0d\n\x0d\n".toUTF8
        let machine0 : Protocol.H1.Machine .receiving := { config := {} }
        let (machine1, _) := (machine0.feed request10).step
        -- Non-empty body: raw bytes must appear in output without chunk framing.
        let body := "hello world".toUTF8
        let machine2 :=
          machine1
          |>.send ({ status := .ok, headers := .empty } : Response.Head)
          |>.sendData #[{ data := body, extensions := #[] }]
          |>.userClosedBody
        let (machine3, step2) := machine2.step
        let output2 := String.fromUTF8! step2.output.toByteArray
        unless output2.contains "hello world" do
          throw <| IO.userError s!"body bytes must appear in output:\n{output2.quote}"
        -- Chunk framing would look like "b\r\nhello world\r\n0\r\n\r\n"
        if output2.contains "0\x0d\x0a\x0d\x0a" then
          throw <| IO.userError s!"body must not be chunk-framed (found final-chunk terminator):\n{output2.quote}"
        unless step2.events.any (fun | .close => true | _ => false) do
          throw <| IO.userError s!"expected .close event after connection-close body:\n{repr step2.events}"
        unless !machine3.keepAlive do
          throw <| IO.userError "keepAlive must be false for HTTP/1.0 connection-close response"

        -- Empty body: userClosedBody with no data must still emit .close.
        let (machine1b, _) := (machine0.feed request10).step
        let machine4 :=
          machine1b
          |>.send ({ status := .ok, headers := .empty } : Response.Head)
          |>.userClosedBody
        let (_, step3) := machine4.step
        unless step3.events.any (fun | .close => true | _ => false) do
          throw <| IO.userError s!"expected .close event for empty HTTP/1.0 body:\n{repr step3.events}")
  ] (·.2)

/-! ## Handler framing vs body (RFC 9112 §6.3) -/

#eval checkCases "Handler framing vs body: async_http_h1_framing_mismatch.lean" #[
    ("An empty body with a handler's `Content-Length`.",
      do
        -- An empty body with a handler's `Content-Length`.
        expect500 "empty body, Content-Length: 1234" <| server get
          |>.setKnownSize (.fixed 0)
          |>.send { status := .ok, headers := headers [(Header.Name.contentLength, "1234")] }),
    ("Framing fields that describe no length.",
      do
        -- Framing fields that describe no length.
        let both := headers [(Header.Name.contentLength, "3"), (Header.Name.transferEncoding, "chunked")]
        expect500 "Content-Length with Transfer-Encoding" <| server get
          |>.send { status := .ok, headers := both }),
    ("Control: matching framing writes the response.",
      do
        -- Control: matching framing writes the response.
        let out ← expectOk "matching Content-Length" <| server
            "GET / HTTP/1.1\r\nHost: a\r\nConnection: close\r\n\r\n"
          |>.setKnownSize (.fixed 3)
          |>.send { status := .ok, headers := headers [(Header.Name.contentLength, "3")] }
          |>.sendData abc |>.userClosedBody
        unless out.startsWith "HTTP/1.1 200 OK\r\n" && out.endsWith "\r\n\r\nabc" do
          throw <| IO.userError s!"matching Content-Length: got\n{out.quote}"),
    ("`Body.stream` sets `chunked` before its producer runs, and a producer may set the length",
      do
        let close := "GET / HTTP/1.1\r\nHost: a\r\nConnection: close\r\n\r\n"
        -- `Body.stream` sets `chunked` before its producer runs, and a producer may set the length
        -- itself before the server reads it: the head's length wins over `chunked` and matches the other.
        for size in [Body.Length.chunked, .fixed 3] do
          let out ← expectOk s!"{repr size}, Content-Length: 3" <| server close
            |>.setKnownSize size
            |>.send { status := .ok, headers := headers [(Header.Name.contentLength, "3")] }
            |>.sendData abc |>.userClosedBody
          unless out.startsWith "HTTP/1.1 200 OK\r\n" && out.contains "Content-Length: 3\r\n" &&
              !out.contains "Transfer-Encoding" && out.endsWith "\r\n\r\nabc" do
            throw <| IO.userError s!"{repr size}, Content-Length: 3: got\n{out.quote}"

        -- A stream longer than its `Content-Length` closes the connection without writing its bytes.
        let some (out, events) := runToHalt (server close
            |>.setKnownSize .chunked
            |>.send { status := .ok, headers := headers [(Header.Name.contentLength, "3")] }
            |>.sendData #[Chunk.ofByteArray "abcd".toUTF8] |>.userClosedBody)
          | throw <| IO.userError "overlong stream: the server never halted"
        unless out.endsWith "Content-Length: 3\r\n\r\n" && events.any (· matches .close) do
          throw <| IO.userError s!"overlong stream: got {repr events}\n{out.quote}"),
    ("streamed body with Content-Length: 3",
      do
        checkTimed "streamed body with Content-Length: 3"
          (raw := mkGetClose)
          (handler := fun _ => Response.ok |>.header! "Content-Length" "3"
            |>.stream fun s => s.send (Chunk.ofByteArray "abc".toUTF8))
          (expect := fun r => do
            assertStatus r "HTTP/1.1 200 OK"
            assertContains r "Content-Length: 3\r\n"
            assertAbsent r "Transfer-Encoding"
            assertContains r "\r\n\r\nabc")),
    ("streamed body longer than its Content-Length: 3",
      do
        checkTimed "streamed body longer than its Content-Length: 3"
          (raw := get)
          (handler := fun _ => Response.ok |>.header! "Content-Length" "3"
            |>.stream fun s => s.send (Chunk.ofByteArray "abcd".toUTF8))
          (expect := fun r => do
            assertStatus r "HTTP/1.1 200 OK"
            assertAbsent r "abc"))
  ] (·.2)


-- RFC 9112 §6.3: a response shorter than its Content-Length is incomplete, so the connection ends.
#eval checkCases "A streamed body shorter than its Content-Length" #[
    ("500 declared, 9 written", do
      let (text, seen, failures) ← serveCounting
        "GET /a HTTP/1.1\x0d\nHost: a\x0d\n\x0d\nGET /b HTTP/1.1\x0d\nHost: a\x0d\n\x0d\n"
        fun _ => Response.ok |>.header! "Content-Length" "500" |>.stream fun s => s.send (Chunk.ofByteArray "123456789".toUTF8)
      ensure (seen == #["/a"]) s!"served {seen}"
      ensure ((text.splitOn "HTTP/1.1 ").length == 2 && text.endsWith "123456789") s!"expected one short response:\n{text.quote}"
      ensure (failures > 0) "onFailure was not called")
  ] (·.2)

#eval checkCases "After a rejected head, a second send writes nothing" #[
    ("Content-Length 1234 for an empty body, then a 200", do
      let m := server get |>.setKnownSize (.fixed 0)
        |>.send { status := .ok, headers := headers [(Header.Name.contentLength, "1234")] }
        |>.sendData abc |>.userClosedBody
      let (m, first) := stepOutput m 8
      ensure (first.startsWith "HTTP/1.1 500") s!"first:\n{first.quote}"
      let (_, second) := stepOutput (m.send { status := .ok } |>.setKnownSize (.fixed 0) |>.userClosedBody) 8
      ensure (second == "") s!"second send wrote:\n{second.quote}")
  ] (·.2)

/-! ## Transfer codings from the handler (RFC 9112 §6.1, RFC 9110 §5.3) -/

#eval checkCases "Transfer codings from the handler: machine" #[
    ("§6.1: server keeps the handler's Transfer-Encoding: gzip, chunked", do
      -- §6.1: a chunked message keeps the transfer codings its body was coded with
      MachineTester.receiving "§6.1: server keeps the handler's Transfer-Encoding: gzip, chunked"
        |>.feed (mkGet "/") |>.step |>.assertIsWaitingMessage
        |>.send { status := .ok, headers := Headers.empty.insert! "Transfer-Encoding" "gzip, chunked" }
        |>.sendBytes "abc".toUTF8 |>.userClosedBody |>.step
        |>.assertOutputContains "Transfer-Encoding: gzip, chunked\r\n" "expected the handler's codings"
        |>.assertOutputContains "3\r\nabc\r\n0\r\n\r\n" "expected a chunked body" |>.run),
    ("§6.1: server keeps the handler's Transfer-Encoding: gzip;level=1, chunked", do
      MachineTester.receiving "§6.1: server keeps the handler's Transfer-Encoding: gzip;level=1, chunked"
        |>.feed (mkGet "/") |>.step |>.assertIsWaitingMessage
        |>.send { status := .ok, headers := Headers.empty.insert! "Transfer-Encoding" "gzip;level=1, chunked" }
        |>.sendBytes "abc".toUTF8 |>.userClosedBody |>.step
        |>.assertOutputContains "Transfer-Encoding: gzip;level=1, chunked\r\n" "expected the handler's codings"
        |>.assertOutputContains "3\r\nabc\r\n0\r\n\r\n" "expected a chunked body" |>.run),
    ("§6.1: server writes the handler's two Transfer-Encoding lines as one", do
      -- RFC 9110 §5.3: codings over several field lines are one list, written as one field
      MachineTester.receiving "§6.1: server writes the handler's two Transfer-Encoding lines as one"
        |>.feed (mkGet "/") |>.step |>.assertIsWaitingMessage
        |>.send { status := .ok, headers :=
          (Headers.empty.insert! "Transfer-Encoding" "gzip").insert! "Transfer-Encoding" "chunked" }
        |>.sendBytes "abc".toUTF8 |>.userClosedBody |>.step
        |>.assertOutputContains "Transfer-Encoding: gzip, chunked\r\n" "expected the combined codings"
        |>.assertOutputNotContains "Transfer-Encoding: chunked\r\n" "expected one Transfer-Encoding field"
        |>.assertOutputContains "3\r\nabc\r\n0\r\n\r\n" "expected a chunked body" |>.run)
  ] (·.2)

/-! ## Chunked writer (RFC 9112 §7.1) -/

#eval checkCases "Chunked writer: machine" #[
    ("§7.1: server sends chunked response — wire encoding correct", do
      -- §7.1: server writes chunk-size lines and terminal 0\r\n\r\n when userClosedBody is called
      let body1 := "Hello, ".toUTF8
      let body2 := "World!".toUTF8
      MachineTester.receiving "§7.1: server sends chunked response — wire encoding correct"
        |>.feed (mkGet "/") |>.step |>.assertIsWaitingMessage
        |>.send { status := .ok } |>.setKnownSize .chunked
        |>.sendBytes body1 |>.step
        |>.sendBytes body2 |>.userClosedBody |>.step
        |>.assertOutputContains "7\r\nHello, \r\n" "expected first chunk in wire output"
        |>.assertOutputContains "6\r\nWorld!\r\n" "expected second chunk in wire output"
        |>.assertOutputContains "0\r\n\r\n" "expected final empty chunk in wire output"
        |>.run)
  ] (·.2)

-- A zero-size chunk is the last-chunk, so the encoder skips empty non-final chunks and later data
-- still reaches the client.
#eval checkCases "Chunked writer: server" #[
    ("empty chunk with extensions before real data — real data still received",
      check "empty chunk with extensions before real data — real data still received"
        (raw := "GET / HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")
        (handler := fun _ => do
          let ext := (Chunk.ExtensionName.ofString! "test", some (Chunk.ExtensionValue.ofString! "val"))
          Response.ok |>.stream fun s => do
            s.send { data := .empty, extensions := #[ext] }
            s.send (Chunk.ofByteArray "after\n".toUTF8))
        (expect := fun r => do
          assertStatus r "HTTP/1.1 200"
          let text := String.fromUTF8! r
          ensure (text.endsWith "after\n\x0d\n0\x0d\n\x0d\n") s!"expected the body to end with the data and one last-chunk:\n{text.quote}"
          ensure ((text.splitOn "\x0d\n0\x0d\n\x0d\n").length == 2) s!"an empty chunk was written as a last-chunk:\n{text.quote}")),
    ("multiple empty chunks before real data — real data still received",
      check "multiple empty chunks before real data — real data still received"
        (raw := "GET / HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")
        (handler := fun _ => do
          Response.ok |>.stream fun s => do
            s.send Chunk.empty
            s.send Chunk.empty
            s.send (Chunk.ofByteArray "data\n".toUTF8))
        (expect := fun r => do
          let text := String.fromUTF8! r
          ensure (text.endsWith "data\n\x0d\n0\x0d\n\x0d\n") s!"expected the body to end with the data and one last-chunk:\n{text.quote}"
          ensure ((text.splitOn "\x0d\n0\x0d\n\x0d\n").length == 2) s!"an empty chunk was written as a last-chunk:\n{text.quote}"))
  ] (·.2)

/-! ## CONNECT (RFC 9110 §9.3.6) -/

#eval checkCases "CONNECT: async_http_connect_response.lean" #[
    ("200 with content",
      do
        check "200 with content" (connectRequest ++ tunnelBytes) handledHandler fun r => do
          assertExact r "HTTP/1.1 200 OK\x0d\nContent-Type: text/plain; charset=utf-8\x0d\nServer: LeanHTTP/1.1\x0d\nConnection: close\x0d\n\x0d\n"
          assertStatus r "HTTP/1.1 200 OK"
          assertResponseCount r 1
          assertAbsent r "Content-Length"
          assertAbsent r "Transfer-Encoding"
          assertAbsent r "handled"
        check "200 streamed" (connectRequest ++ tunnelBytes)
          (fun _ => Response.ok |>.stream fun out => out.send (Chunk.ofByteArray "tunnel".toUTF8))
          fun r => do
            assertResponseCount r 1
            assertAbsent r "Transfer-Encoding"
            assertAbsent r "tunnel"),
    ("403",
      do
        checkClose "403" connectRequest (fun _ => Response.forbidden |>.text "no") fun r => do
          assertStatus r "HTTP/1.1 403"
          assertContains r "Content-Length: 2"
          assertContains r "\x0d\n\x0d\nno")
  ] (·.2)
