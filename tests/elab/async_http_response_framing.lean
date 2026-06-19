import Std.Http.Test.Helpers

open Std.Async
open Std Http Internal Test

-- Shared fixtures

private def ok200Head : String :=
  "HTTP/1.1 200 OK\x0d\nContent-Type: text/plain; charset=utf-8\x0d\nServer: LeanHTTP/1.1\x0d\nConnection: close\x0d\nContent-Length: 2\x0d\n\x0d\n"

-- RFC 9110 §9.3.2: HEAD

#eval runGroup "RFC 9110 §9.3.2: HEAD response framing" do
  check "HEAD omits body bytes, preserves headers"
    (raw := "HEAD / HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")
    (handler := okHandler)
    (expect := fun r => assertExact r ok200Head)

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
      assertAbsent headResp "hello")

-- RFC 9110 §15.4: 304 and 204 response framing

#eval runGroup "RFC 9110 §15.4: 304 Not Modified strips framing headers" do
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
    throw <| IO.userError s!"unexpected framing headers in 304:\n{text304.quote}"

#eval runGroup "RFC 9110 §15.3.5: 204 No Content strips framing headers" do
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
    throw <| IO.userError s!"unexpected framing headers in 204:\n{text204.quote}"

-- RFC 9112 §9.6: Client-mode — parsing responses

#eval runGroup "RFC 9112 §9.6: client-mode response parsing" do
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
    throw <| IO.userError "missing Content-Length header in parsed response"

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
    throw <| IO.userError s!"expected 5 unread bytes, got {machineC'.reader.input.remainingBytes}"

-- RFC 9110 §15.2: 1xx informational responses MUST NOT carry framing headers

#eval runGroup "RFC 9110 §15.2: 1xx informational responses strip framing headers" do
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
    throw <| IO.userError s!"Content-Length must be preserved in final response:\n{text200.quote}"

-- RFC 7230 §3.3.1 / RFC 9112 §6.1: HTTP/1.0 connection-close framing.
-- When the handler does not set Content-Length for an HTTP/1.0 request the machine
-- must not emit Transfer-Encoding or Content-Length; it writes raw bytes and closes.

#eval runGroup "RFC 7230 §3.3.1: HTTP/1.0 connection-close — headers" do
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
    throw <| IO.userError s!"Content-Length must not appear when body length is unknown:\n{textA.quote}"

#eval runGroup "RFC 7230 §3.3.1: HTTP/1.0 connection-close — body framing" do
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
    throw <| IO.userError s!"expected .close event for empty HTTP/1.0 body:\n{repr step3.events}"
