import Std.Internal.Http
import Std.Internal.Async

open Std.Internal.IO Async
open Std Http

abbrev TestHandler := Request Body.Incoming → ContextAsync (Response Body.AnyBody)

instance : Std.Http.Server.Handler TestHandler where
  onRequest handler request := handler request

instance : Coe (ContextAsync (Response Body.Incoming)) (ContextAsync (Response Body.AnyBody)) where
  coe action := do
    let response ← action
    pure { response with body := Body.Internal.incomingToOutgoing response.body }

instance : Coe (Async (Response Body.Incoming)) (ContextAsync (Response Body.AnyBody)) where
  coe action := do
    let response ← action
    pure { response with body := Body.Internal.incomingToOutgoing response.body }

structure RejectContinueHandler where
  onRequestCalls : IO.Ref Nat

instance : Std.Http.Server.Handler RejectContinueHandler where
  onRequest self _request := do
    self.onRequestCalls.modify (· + 1)
    Response.ok |>.text "request-ran"

  onContinue _self _head :=
    pure false

structure AcceptContinueHandler where
  onRequestCalls : IO.Ref Nat

instance : Std.Http.Server.Handler AcceptContinueHandler where
  onRequest self request := do
    self.onRequestCalls.modify (· + 1)
    let body : String ← request.body.readAll
    Response.ok |>.text s!"accepted:{body}"

  onContinue _self _head :=
    pure true


def sendRaw {σ : Type} [Std.Http.Server.Handler σ]
    (client : Mock.Client)
    (server : Mock.Server)
    (raw : ByteArray)
    (handler : σ)
    (config : Config := { lingeringTimeout := 3000, generateDate := false }) : IO ByteArray := Async.block do
  client.send raw
  Std.Http.Server.serveConnection server handler config
    |>.run
  let res ← client.recv?
  pure (res.getD .empty)


def assertContains (name : String) (response : ByteArray) (needle : String) : IO Unit := do
  let text := String.fromUTF8! response
  unless text.contains needle do
    throw <| IO.userError s!"Test '{name}' failed:\nExpected to contain: {needle.quote}\nGot:\n{text.quote}"


def assertNotContains (name : String) (response : ByteArray) (needle : String) : IO Unit := do
  let text := String.fromUTF8! response
  if text.contains needle then
    throw <| IO.userError s!"Test '{name}' failed:\nDid not expect: {needle.quote}\nGot:\n{text.quote}"


def assertCallCount (name : String) (calls : IO.Ref Nat) (expected : Nat) : IO Unit := do
  let got ← calls.get
  if got != expected then
    throw <| IO.userError s!"Test '{name}' failed:\nExpected onRequest calls {expected}, got {got}"


def countOccurrences (s : String) (needle : String) : Nat :=
  if needle.isEmpty then
    0
  else
    (s.splitOn needle).length - 1


def assertOccurrenceCount (name : String) (response : ByteArray) (needle : String) (expected : Nat) : IO Unit := do
  let text := String.fromUTF8! response
  let got := countOccurrences text needle
  if got != expected then
    throw <| IO.userError s!"Test '{name}' failed:\nExpected {expected} occurrences of {needle.quote}, got {got}\n{text.quote}"


-- Rejecting Expect returns 417 and does not execute user handler.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let calls ← IO.mkRef 0
  let handler : RejectContinueHandler := { onRequestCalls := calls }

  let raw := "POST /upload HTTP/1.1\x0d\nHost: example.com\x0d\nExpect: 100-continue\x0d\nContent-Length: 5\x0d\nConnection: close\x0d\n\x0d\nhello".toUTF8
  let response ← sendRaw client server raw handler

  assertContains "Expect rejected status" response "HTTP/1.1 417 Expectation Failed"
  assertNotContains "Expect rejected no 100 Continue" response "100 Continue"
  assertNotContains "Expect rejected no handler body" response "request-ran"
  assertOccurrenceCount "Expect rejected single response" response "HTTP/1.1 " 1
  assertCallCount "Expect rejected call count" calls 0

-- Rejected Expect closes the exchange and blocks pipelined follow-up requests.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let calls ← IO.mkRef 0
  let handler : RejectContinueHandler := { onRequestCalls := calls }

  let req1 := "POST /first HTTP/1.1\x0d\nHost: example.com\x0d\nExpect: 100-continue\x0d\nContent-Length: 5\x0d\n\x0d\nhello"
  let req2 := "GET /second HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n"
  let response ← sendRaw client server (req1 ++ req2).toUTF8 handler

  assertContains "Expect rejected still 417" response "HTTP/1.1 417 Expectation Failed"
  assertNotContains "Expect rejected no second request" response "/second"
  assertCallCount "Expect rejected pipelined call count" calls 0

-- Accepted Expect emits 100 Continue followed by final 200.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let calls ← IO.mkRef 0
  let handler : AcceptContinueHandler := { onRequestCalls := calls }

  let raw := "POST /ok HTTP/1.1\x0d\nHost: example.com\x0d\nExpect: 100-continue\x0d\nContent-Length: 5\x0d\nConnection: close\x0d\n\x0d\nhello".toUTF8
  let response ← sendRaw client server raw handler

  assertContains "Expect accepted has 100" response "HTTP/1.1 100 Continue"
  assertContains "Expect accepted has final 200" response "HTTP/1.1 200 OK"
  assertContains "Expect accepted body" response "accepted:hello"
  assertOccurrenceCount "Expect accepted exactly one 100" response "HTTP/1.1 100 Continue" 1
  assertOccurrenceCount "Expect accepted exactly one 200" response "HTTP/1.1 200 OK" 1
  assertCallCount "Expect accepted call count" calls 1

-- Non-100 Expect token proceeds as a normal request.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let calls ← IO.mkRef 0
  let handler : RejectContinueHandler := { onRequestCalls := calls }

  let raw := "POST /odd HTTP/1.1\x0d\nHost: example.com\x0d\nExpect: something-else\x0d\nContent-Length: 5\x0d\nConnection: close\x0d\n\x0d\nhello".toUTF8
  let response ← sendRaw client server raw handler

  assertContains "Non-100 Expect status" response "HTTP/1.1 200 OK"
  assertContains "Non-100 Expect handler ran" response "request-ran"
  assertNotContains "Non-100 Expect no 100 Continue" response "100 Continue"
  assertCallCount "Non-100 Expect call count" calls 1

-- h11-inspired: Expect token matching is case-insensitive.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let calls ← IO.mkRef 0
  let handler : AcceptContinueHandler := { onRequestCalls := calls }

  let raw := "POST /case HTTP/1.1\x0d\nHost: example.com\x0d\nExpect: 100-CONTINUE\x0d\nContent-Length: 5\x0d\nConnection: close\x0d\n\x0d\nhello".toUTF8
  let response ← sendRaw client server raw handler

  assertContains "Case-insensitive Expect has 100" response "HTTP/1.1 100 Continue"
  assertContains "Case-insensitive Expect final 200" response "HTTP/1.1 200 OK"
  assertCallCount "Case-insensitive Expect call count" calls 1

-- Normal requests without Expect do not emit 100 Continue.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let calls ← IO.mkRef 0
  let handler : AcceptContinueHandler := { onRequestCalls := calls }

  let raw := "POST /no-expect HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 5\x0d\nConnection: close\x0d\n\x0d\nhello".toUTF8
  let response ← sendRaw client server raw handler

  assertContains "No Expect status" response "HTTP/1.1 200 OK"
  assertContains "No Expect body" response "accepted:hello"
  assertNotContains "No Expect no interim 100" response "100 Continue"
  assertOccurrenceCount "No Expect exactly one 200" response "HTTP/1.1 200 OK" 1
  assertCallCount "No Expect call count" calls 1

-- Date header is generated when enabled.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "GET /date HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let handler : TestHandler := fun _ => Response.ok |>.text "hello"
  let response ← sendRaw client server raw handler (config := { lingeringTimeout := 3000, generateDate := true })

  assertContains "Date generated status" response "HTTP/1.1 200 OK"
  assertContains "Date generated header" response "Date: "

-- Date header is absent when disabled.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "GET /no-date HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let handler : TestHandler := fun _ => Response.ok |>.text "hello"
  let response ← sendRaw client server raw handler (config := { lingeringTimeout := 3000, generateDate := false })

  assertContains "Date disabled status" response "HTTP/1.1 200 OK"
  assertNotContains "Date disabled header" response "Date: "

-- User-specified Date header is preserved and not duplicated.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "GET /custom-date HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let handler : TestHandler := fun _ =>
    Response.ok
      |>.header! "Date" "Mon, 01 Jan 2024 00:00:00 GMT"
      |>.text "hello"
  let response ← sendRaw client server raw handler (config := { lingeringTimeout := 3000, generateDate := true })

  assertContains "User Date preserved" response "Date: Mon, 01 Jan 2024 00:00:00 GMT"

  let text := String.fromUTF8! response
  let count := countOccurrences text "Date: "
  if count != 1 then
    throw <| IO.userError s!"Test 'User Date not duplicated' failed:\nExpected one Date header, got {count}\n{text.quote}"
