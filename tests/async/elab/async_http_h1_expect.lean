module

import Std.Http.Test.Helpers
import Std.Http.Test.Machine

/-!
# HTTP/1.1 `Expect: 100-continue`

How a server answers `Expect: 100-continue`: on the machine (`canContinue`, interim and final
responses while the decision is pending) and through `serveConnection` with `Handler.onContinue`.
RFC 9110 §10.1.1, §15.2, §15.5.18.
-/

open Std Http
open Std.Http.Protocol.H1
open Std.Http.Internal.Test

private def mkPostHead (path : String) (bodyLen : Nat) (extra : String := "") : String :=
  rawRequest "POST" path (extra := s!"Content-Length: {bodyLen}\r\n{extra}")

private structure RejectContinueHandler where
  onRequestCalls : IO.Ref Nat

private instance : Server.Handler RejectContinueHandler where
  onRequest self _ := do
    self.onRequestCalls.modify (· + 1)
    Response.ok |>.text "request-ran"
  onContinue _ _ := pure false

private structure AcceptContinueHandler where
  onRequestCalls : IO.Ref Nat

private instance : Server.Handler AcceptContinueHandler where
  onRequest self request := do
    self.onRequestCalls.modify (· + 1)
    let body : String ← request.body.readAll
    Response.ok |>.text s!"accepted:{body}"
  onContinue _ _ := pure true

private def checkH {σ : Type} [Server.Handler σ] (name : String) (raw : String) (handler : σ)
    (expect : ByteArray → IO Unit) (config : Std.Http.Config := defaultConfig) : IO Unit := do
  try expect (← serveRaw raw handler config)
  catch e => throw (IO.userError s!"[{name}] {e}")

private def assertCallCount (ref : IO.Ref Nat) (expected : Nat) : IO Unit := do
  let got ← ref.get
  unless got == expected do
    throw <| IO.userError s!"expected {expected} onRequest calls, got {got}"

private def expectRequest : String :=
  "POST / HTTP/1.1\r\nHost: a\r\nExpect: 100-continue\r\nContent-Length: 5\r\n\r\n"

/-- Steps `machine` until it halts. Returns its output, or `none` if it has not halted after 16 steps. -/
private def outputToHalt (machine : Machine .receiving) : Option String :=
  (runToHalt machine).map (·.1)

/-! ## Machine (RFC 9110 §10.1.1, §15.2) -/

#eval checkCases "Machine: machine" #[
    ("§10.1.1: Expect:100-continue accepted → body readable", do
      -- accepted: body becomes readable after canContinue .continue
      let body := "hello".toUTF8
      MachineTester.receiving "§10.1.1: Expect:100-continue accepted → body readable"
        |>.feed (mkPostHead "/upload" body.size "Expect: 100-continue\r\n")
        |>.step |>.assertHasEndHeaders |>.assertHasContinue
        |>.canContinue .«continue»
        |>.feedBytes body |>.step |>.assertCanPullBodyNow
        |>.drainBody |>.assertPulledBody body |>.run),
    ("§15.5.18: Expect:100-continue rejected → reader closed", do
      -- rejected: reader closed, body not delivered
      MachineTester.receiving "§15.5.18: Expect:100-continue rejected → reader closed"
        |>.feed (mkPostHead "/upload" 5 "Expect: 100-continue\r\n")
        |>.step |>.assertHasContinue
        |>.canContinue .expectationFailed
        |>.assertReaderClosed
        |>.assert (fun m => !m.canPullBody) "body must not be pullable after rejection" |>.run),
    ("§10.1.1: Expect:100-continue + Content-Length:0 → empty body after acceptance", do
      -- CL:0 + Expect:100-continue → empty body after acceptance
      MachineTester.receiving "§10.1.1: Expect:100-continue + Content-Length:0 → empty body after acceptance"
        |>.feed "POST / HTTP/1.1\r\nHost: example.com\r\nContent-Length: 0\r\nExpect: 100-continue\r\n\r\n"
        |>.step |>.assertHasEndHeaders |>.assertHasContinue
        |>.canContinue .«continue»
        |>.pullBody |>.assertPulledBody .empty |>.assertLastChunkFinal |>.run),
    ("§10.1.1, §15.5.18: final response sent while the reader awaits canContinue → .close", do
      -- §15.5.14: writer completing a non-1xx response while reader is in .continue state
      --           must force-close the reader (body will never arrive after rejection)
      MachineTester.receiving "§10.1.1, §15.5.18: final response sent while the reader awaits canContinue → .close"
        |>.feed (mkPostHead "/upload" 5 "Expect: 100-continue\r\n")
        |>.step |>.assertHasContinue
        |>.send { status := .expectationFailed } |>.setKnownSize (.fixed 0) |>.userClosedBody
        |>.step
        |>.assertHasEvent (fun | .close => true | _ => false)
            "expected .close: writer completed after rejecting Expect: 100-continue, body will never arrive"
        |>.run),
    ("§10.1.1: 1xx interim response while reader awaits canContinue → writer stays open", do
      -- §15.2: 1xx responses are valid while awaiting canContinue; writer must remain open
      MachineTester.receiving "§10.1.1: 1xx interim response while reader awaits canContinue → writer stays open"
        |>.feed (mkPostHead "/upload" 5 "Expect: 100-continue\r\n")
        |>.step |>.assertHasContinue
        |>.send { status := .processing } |>.step
        |>.assertIsWaitingMessage |>.run),
    ("§15.5: a 417 from canContinue explains itself", do
      MachineTester.receiving "§15.5: a 417 from canContinue explains itself"
        |>.feed (mkPostHead "/" 5 "Expect: 100-continue\r\n") |>.step |>.assertHasContinue
        |>.canContinue .expectationFailed |>.step
        |>.assertOutputStartsWith "HTTP/1.1 417 Expectation Failed\r\n" "expected 417"
        |>.assertOutputContains "Content-Length: 19\r\n\r\nExpectation Failed\n" "expected an explanation"
        |>.assertNotKeepAlive |>.run),
    ("§15.5: canContinue after a final response leaves that response intact", do
      -- A final response sent before the rejection keeps its length and body; the rejection only stops
      -- the request body and the connection
      MachineTester.receiving "§15.5: canContinue after a final response leaves that response intact"
        |>.feed (mkPostHead "/" 5 "Expect: 100-continue\r\n") |>.step |>.assertHasContinue
        |>.setKnownSize (.fixed 5) |>.send { status := .ok } |>.sendBytes "hello".toUTF8 |>.userClosedBody
        |>.canContinue .expectationFailed |>.step |>.step
        |>.assertOutputStartsWith "HTTP/1.1 200 OK\r\nConnection: close\r\nContent-Length: 5\r\n\r\nhello"
            "expected the 200 with its own length and body"
        |>.assertOutputNotContains "Expectation Failed" "no 417 content after a final response"
        |>.assertNoError |>.assertNotKeepAlive |>.run)
  ] (·.2)

#eval checkCases "Machine: async_http_h1_expect_final_response.lean" #[
    ("A `canContinue` after the final response writes nothing more.",
      show IO Unit from do
      let machine := (({ config := {} } : Machine .receiving).feed expectRequest.toUTF8).step.1
      let answered := machine.setKnownSize (.fixed 2) |>.send { status := .ok }
        |>.sendData #[Chunk.ofByteArray "ok".toUTF8] |>.userClosedBody
      let some out := outputToHalt answered
        | throw <| IO.userError "the machine did not halt after its final response"
      unless out == "HTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\nok" do
        throw <| IO.userError s!"unexpected output {out.quote}"
      -- A `canContinue` after the final response writes nothing more.
      let some out := outputToHalt (answered.step.1.canContinue .«continue»)
        | throw <| IO.userError "the machine did not halt after a late canContinue"
      unless out.isEmpty do
        throw <| IO.userError s!"a late canContinue wrote {out.quote}")
  ] (·.2)


-- RFC 9110 §10.1.1: a server that answers before reading the body SHOULD close the connection.
#eval checkCases "A final response while the 100-continue decision is pending" #[
    ("its head says Connection: close", MachineTester.receiving "final response before canContinue"
      |>.feed (mkPostHead "/upload" 5 "Expect: 100-continue\r\n") |>.step |>.assertHasContinue
      |>.send { status := .ok } |>.setKnownSize (.fixed 0) |>.userClosedBody |>.step |>.step
      |>.assertOutputStartsWith "HTTP/1.1 200 OK\r\n" "expected the 200"
      |>.assertOutputContains "Connection: close\r\n" "expected Connection: close" |>.run)
  ] (·.2)

-- RFC 9110 §10.1.1: a server MUST ignore `Expect: 100-continue` in an HTTP/1.0 request.
#eval checkCases "HTTP/1.0 with Expect: 100-continue: machine" #[
    ("no continue event, the body is readable", MachineTester.receiving "HTTP/1.0 Expect"
      |>.feed "POST / HTTP/1.0\r\nExpect: 100-continue\r\nContent-Length: 5\r\n\r\nhello" |>.step
      |>.assertNoError |>.assertHasEndHeaders |>.assertNoEvent (· matches .«continue») "no continue event for HTTP/1.0"
      |>.drainBody |>.assertPulledBody "hello".toUTF8 |>.run)
  ] (·.2)

/-! ## Server (RFC 9110 §10.1.1, §15.5.18) -/

#eval checkCases "Server: async_http_expect.lean" #[
    ("rejected Expect → 417, handler not called",
      do
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

        assertCallCount calls 0),
    ("rejected Expect closes exchange, blocks pipelined second request",
      do
        let calls ← IO.mkRef 0
        let handler : RejectContinueHandler := { onRequestCalls := calls }
        checkH "rejected Expect closes exchange, blocks pipelined second request"
          (raw :=
            "POST /first HTTP/1.1\x0d\nHost: example.com\x0d\nExpect: 100-continue\x0d\nContent-Length: 5\x0d\n\x0d\nhello" ++
            "GET /second HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")
          (handler := handler)
          (expect := fun r =>
            assertContains r "HTTP/1.1 417 Expectation Failed" *>
            assertResponseCount r 1)

        assertCallCount calls 0),
    ("accepted Expect → 100 Continue then 200",
      do
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

        assertCallCount calls 1),
    ("non-100 Expect token → normal request, no interim",
      do
        let rejectCalls ← IO.mkRef 0
        let rejectHandler : RejectContinueHandler := { onRequestCalls := rejectCalls }
        checkH "non-100 Expect token → normal request, no interim"
          (raw := "POST /odd HTTP/1.1\x0d\nHost: example.com\x0d\nExpect: something-else\x0d\nContent-Length: 5\x0d\nConnection: close\x0d\n\x0d\nhello")
          (handler := rejectHandler)
          (expect := fun r =>
            assertContains r "HTTP/1.1 200 OK" *>
            assertContains r "request-ran" *>
            assertAbsent r "100 Continue")

        assertCallCount rejectCalls 1),
    ("Expect: 100-CONTINUE (case-insensitive) → 100 then 200",
      do
        let acceptCalls ← IO.mkRef 0
        let acceptHandler : AcceptContinueHandler := { onRequestCalls := acceptCalls }
        checkH "Expect: 100-CONTINUE (case-insensitive) → 100 then 200"
          (raw := "POST /case HTTP/1.1\x0d\nHost: example.com\x0d\nExpect: 100-CONTINUE\x0d\nContent-Length: 5\x0d\nConnection: close\x0d\n\x0d\nhello")
          (handler := acceptHandler)
          (expect := fun r =>
            assertContains r "HTTP/1.1 100 Continue" *>
            assertContains r "HTTP/1.1 200 OK")

        assertCallCount acceptCalls 1),
    ("no Expect header → no 100 Continue emitted",
      do
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

        assertCallCount noCalls 1)
  ] (·.2)


private structure CountContinue where
  continues : IO.Ref Nat

private instance : Server.Handler CountContinue where
  onRequest _ request := do
    let body : String ← request.body.readAll
    Response.ok |>.text s!"accepted:{body}"
  onContinue self _ := do
    self.continues.modify (· + 1)
    pure true

#eval checkCases "HTTP/1.0 with Expect: 100-continue: server" #[
    ("no 100, onContinue not called, body read", do
      let continues ← IO.mkRef 0
      let r ← serveRaw "POST / HTTP/1.0\x0d\nExpect: 100-continue\x0d\nContent-Length: 5\x0d\n\x0d\nhello" ({ continues } : CountContinue)
        (closeInput := true)
      (Want.all [.status "HTTP/1.1 200", .absent "100 Continue", .contains "accepted:hello"]).check r
      ensure ((← continues.get) == 0) s!"onContinue was called {← continues.get} times")
  ] (·.2)

#eval checkCases "Expect: 100-continue without a Content-Length body" #[
    ("Content-Length: 0", "POST / HTTP/1.1\x0d\nHost: a\x0d\nExpect: 100-continue\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\n\x0d\n",
      Want.all [.contains "HTTP/1.1 200 OK", .contains "accepted:"]),
    ("no framing", "GET / HTTP/1.1\x0d\nHost: a\x0d\nExpect: 100-continue\x0d\nConnection: close\x0d\n\x0d\n",
      .all [.contains "HTTP/1.1 200 OK", .contains "accepted:"]),
    ("chunked", "POST / HTTP/1.1\x0d\nHost: a\x0d\nExpect: 100-continue\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n",
      .all [.status "HTTP/1.1 100 Continue", .contains "HTTP/1.1 200 OK", .contains "accepted:hello"])
  ] fun (_, raw, want) => do
    let calls ← IO.mkRef 0
    want.check (← serveRaw raw ({ onRequestCalls := calls } : AcceptContinueHandler) (closeInput := true))

-- RFC 9110 §10.1.1: a client may send the body without waiting; a 100 only ever precedes its own final response.
#eval checkCases "Two pipelined Expect requests with their bodies" #[
    ("both served in order, no stray 100", do
      let calls ← IO.mkRef 0
      let r ← serveRaw ("POST /1 HTTP/1.1\x0d\nHost: a\x0d\nExpect: 100-continue\x0d\nContent-Length: 5\x0d\n\x0d\nhello" ++
          "POST /2 HTTP/1.1\x0d\nHost: a\x0d\nExpect: 100-continue\x0d\nContent-Length: 5\x0d\nConnection: close\x0d\n\x0d\nworld")
        ({ onRequestCalls := calls } : AcceptContinueHandler) (closeInput := true)
      let text := String.fromUTF8! r
      let codes := (text.splitOn "HTTP/1.1 ").drop 1 |>.map fun c => String.ofList (c.toList.take 3)
      ensure ((codes.filter (· == "200")).length == 2) s!"statuses {codes}"
      ensure (codes.getLast? == some "200" && !(codes.zip (codes.drop 1)).any (· == ("100", "100"))) s!"stray 100: {codes}"
      let some i := (text.splitOn "accepted:hello").head?.map (·.length) | throw <| IO.userError "no first body"
      let some j := (text.splitOn "accepted:world").head?.map (·.length) | throw <| IO.userError "no second body"
      ensure (i < j && text.contains "accepted:hello" && text.contains "accepted:world") s!"out of order:\n{text.quote}")
  ] (·.2)

private def expectField : TestHandler := fun req =>
  Response.ok |>.text ((req.line.headers.get? (.ofString! "Expect")).map (·.value) |>.getD "<none>")

#eval checkCases "Expect accepted, the handler does not read the body" #[
    ("no hang, and the handler sees Expect", checkHandler
      "POST / HTTP/1.1\x0d\nHost: a\x0d\nExpect: 100-continue\x0d\nContent-Length: 5\x0d\n\x0d\nhello" expectField
      (.all [.contains "HTTP/1.1 200 OK", .contains "\x0d\n\x0d\n100-continue"]) (closeInput := true))
  ] (·.2)
