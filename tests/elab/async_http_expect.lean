import Std.Http.Test.Helpers

open Std.Async
open Std Http Internal Test

-- Handlers for Expect: 100-continue testing

private structure RejectContinueHandler where
  onRequestCalls : IO.Ref Nat

instance : Std.Http.Server.Handler RejectContinueHandler where
  onRequest self _ := do
    self.onRequestCalls.modify (· + 1)
    Response.ok |>.text "request-ran"

  onContinue _ _ := pure false

private structure AcceptContinueHandler where
  onRequestCalls : IO.Ref Nat

instance : Std.Http.Server.Handler AcceptContinueHandler where
  onRequest self request := do
    self.onRequestCalls.modify (· + 1)
    let body : String ← request.body.readAll
    Response.ok |>.text s!"accepted:{body}"

  onContinue _ _ := pure true

-- Per-test runner for generic handlers

private def checkH {σ : Type} [Std.Http.Server.Handler σ]
    (name : String)
    (raw : String)
    (handler : σ)
    (expect : ByteArray → IO Unit)
    (config : Config := defaultConfig) : IO Unit := do
  let (client, server) ← Mock.new
  let response ← Async.block do
    client.send raw.toUTF8
    Std.Http.Server.serveConnection server handler config |>.run
    return (← client.recv?).getD .empty

  try expect response
  catch e => throw (IO.userError s!"[{name}] {e}")

private def assertCallCount (ref : IO.Ref Nat) (expected : Nat) : IO Unit := do
  let got ← ref.get
  unless got == expected do
    throw <| IO.userError s!"expected {expected} onRequest calls, got {got}"

-- RFC 9110 §10.1.1: Expect: 100-continue

#eval runGroup "Expect: 100-continue — reject" do
  let calls ← IO.mkRef 0
  let handler : RejectContinueHandler := { onRequestCalls := calls }

  checkH "rejected Expect → 417, handler not called"
    (raw := "POST /upload HTTP/1.1\x0d\nHost: example.com\x0d\nExpect: 100-continue\x0d\nContent-Length: 5\x0d\nConnection: close\x0d\n\x0d\nhello")
    (handler := handler)
    (expect := fun r =>
      assertContains r "HTTP/1.1 417 Expectation Failed" *>
      assertAbsent r "100 Continue" *>
      assertAbsent r "request-ran" *>
      assertResponseCount r 1)

  assertCallCount calls 0

#eval runGroup "Expect: 100-continue — reject blocks pipelining" do
  let calls ← IO.mkRef 0
  let handler : RejectContinueHandler := { onRequestCalls := calls }

  checkH "rejected Expect closes exchange, blocks pipelined second request"
    (raw :=
      "POST /first HTTP/1.1\x0d\nHost: example.com\x0d\nExpect: 100-continue\x0d\nContent-Length: 5\x0d\n\x0d\nhello" ++
      "GET /second HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")
    (handler := handler)
    (expect := fun r =>
      assertContains r "HTTP/1.1 417 Expectation Failed" *>
      assertAbsent r "/second")

  assertCallCount calls 0

#eval runGroup "Expect: 100-continue — accept" do
  let calls ← IO.mkRef 0
  let handler : AcceptContinueHandler := { onRequestCalls := calls }

  checkH "accepted Expect → 100 Continue then 200"
    (raw := "POST /ok HTTP/1.1\x0d\nHost: example.com\x0d\nExpect: 100-continue\x0d\nContent-Length: 5\x0d\nConnection: close\x0d\n\x0d\nhello")
    (handler := handler)
    (expect := fun r =>
      assertContains r "HTTP/1.1 100 Continue" *>
      assertContains r "HTTP/1.1 200 OK" *>
      assertContains r "accepted:hello" *>
      assertResponseCount r 2)  -- one interim + one final

  assertCallCount calls 1

#eval runGroup "Expect: misc" do
  let rejectCalls ← IO.mkRef 0
  let rejectHandler : RejectContinueHandler := { onRequestCalls := rejectCalls }

  checkH "non-100 Expect token → normal request, no interim"
    (raw := "POST /odd HTTP/1.1\x0d\nHost: example.com\x0d\nExpect: something-else\x0d\nContent-Length: 5\x0d\nConnection: close\x0d\n\x0d\nhello")
    (handler := rejectHandler)
    (expect := fun r =>
      assertContains r "HTTP/1.1 200 OK" *>
      assertContains r "request-ran" *>
      assertAbsent r "100 Continue")

  assertCallCount rejectCalls 1

  let acceptCalls ← IO.mkRef 0
  let acceptHandler : AcceptContinueHandler := { onRequestCalls := acceptCalls }

  checkH "Expect: 100-CONTINUE (case-insensitive) → 100 then 200"
    (raw := "POST /case HTTP/1.1\x0d\nHost: example.com\x0d\nExpect: 100-CONTINUE\x0d\nContent-Length: 5\x0d\nConnection: close\x0d\n\x0d\nhello")
    (handler := acceptHandler)
    (expect := fun r =>
      assertContains r "HTTP/1.1 100 Continue" *>
      assertContains r "HTTP/1.1 200 OK")

  assertCallCount acceptCalls 1

  let noCalls ← IO.mkRef 0
  let noExpectHandler : AcceptContinueHandler := { onRequestCalls := noCalls }

  checkH "no Expect header → no 100 Continue emitted"
    (raw := "POST /no-expect HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 5\x0d\nConnection: close\x0d\n\x0d\nhello")
    (handler := noExpectHandler)
    (expect := fun r =>
      assertContains r "HTTP/1.1 200 OK" *>
      assertContains r "accepted:hello" *>
      assertAbsent r "100 Continue" *>
      assertResponseCount r 1)

  assertCallCount noCalls 1

-- Date header generation

#eval runGroup "Date header" do
  check "generateDate: true adds Date header"
    (raw := mkGetClose "/date")
    (handler := fun _ => Response.ok |>.text "hello")
    (config := { defaultConfig with generateDate := true })
    (expect := fun r =>
      assertStatus r "HTTP/1.1 200" *>
      assertContains r "Date: ")

  check "generateDate: false omits Date header"
    (raw := mkGetClose "/no-date")
    (handler := fun _ => Response.ok |>.text "hello")
    (config := { defaultConfig with generateDate := false })
    (expect := fun r =>
      assertStatus r "HTTP/1.1 200" *>
      assertAbsent r "Date: ")

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
        throw <| IO.userError s!"expected 1 Date header, got {count}:\n{text.quote}")
