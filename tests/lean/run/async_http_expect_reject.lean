import Std.Internal.Http
import Std.Internal.Async

open Std.Internal.IO Async
open Std Http

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
  let responseStr := String.fromUTF8! response
  unless responseStr.contains needle do
    throw <| IO.userError s!"Test '{name}' failed:\nExpected to contain: {needle.quote}\nGot:\n{responseStr.quote}"

def assertNotContains (name : String) (response : ByteArray) (needle : String) : IO Unit := do
  let responseStr := String.fromUTF8! response
  if responseStr.contains needle then
    throw <| IO.userError s!"Test '{name}' failed:\nDid not expect to contain: {needle.quote}\nGot:\n{responseStr.quote}"

-- Rejecting Expect must return 401, skip 100 Continue, and never run onRequest.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let calls ← IO.mkRef 0
  let handler : RejectContinueHandler := { onRequestCalls := calls }

  let raw := "POST /upload HTTP/1.1\x0d\nHost: example.com\x0d\nExpect: 100-continue\x0d\nContent-Length: 5\x0d\nConnection: close\x0d\n\x0d\nhello".toUTF8
  let response ← sendRaw client server raw handler

  assertContains "Expect rejected returns 401" response "HTTP/1.1 401 Unauthorized"
  assertNotContains "Expect rejected no 100 Continue" response "100 Continue"
  assertNotContains "Expect rejected no user response body" response "request-ran"

  let count ← calls.get
  if count != 0 then
    throw <| IO.userError s!"Expected onRequest not to run when continue is rejected, but call count was {count}"

-- Rejected Expect should also close the exchange and not process a pipelined second request.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let calls ← IO.mkRef 0
  let handler : RejectContinueHandler := { onRequestCalls := calls }

  let req1 := "POST /first HTTP/1.1\x0d\nHost: example.com\x0d\nExpect: 100-continue\x0d\nContent-Length: 5\x0d\n\x0d\nhello"
  let req2 := "GET /second HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n"
  let response ← sendRaw client server (req1 ++ req2).toUTF8 handler

  assertContains "Expect rejected still 401" response "HTTP/1.1 401 Unauthorized"
  assertNotContains "Expect rejected should not process second request" response "/second"

  let count ← calls.get
  if count != 0 then
    throw <| IO.userError s!"Expected onRequest to stay at 0 after rejected continue with pipelining, got {count}"

-- Accepting Expect should emit 100 Continue and then final response.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let calls ← IO.mkRef 0
  let handler : AcceptContinueHandler := { onRequestCalls := calls }

  let raw := "POST /ok HTTP/1.1\x0d\nHost: example.com\x0d\nExpect: 100-continue\x0d\nContent-Length: 5\x0d\nConnection: close\x0d\n\x0d\nhello".toUTF8
  let response ← sendRaw client server raw handler

  assertContains "Expect accepted sends 100" response "HTTP/1.1 100 Continue"
  assertContains "Expect accepted sends 200" response "HTTP/1.1 200 OK"
  assertContains "Expect accepted body echo" response "accepted:hello"

  let count ← calls.get
  if count != 1 then
    throw <| IO.userError s!"Expected exactly one onRequest call when continue is accepted, got {count}"

-- Non-100 Expect value should not trigger continue handling and should proceed normally.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let calls ← IO.mkRef 0
  let handler : RejectContinueHandler := { onRequestCalls := calls }

  let raw := "POST /odd HTTP/1.1\x0d\nHost: example.com\x0d\nExpect: something-else\x0d\nContent-Length: 5\x0d\nConnection: close\x0d\n\x0d\nhello".toUTF8
  let response ← sendRaw client server raw handler

  assertContains "Non-100 Expect gets normal response" response "HTTP/1.1 200 OK"
  assertContains "Non-100 Expect handler ran" response "request-ran"
  assertNotContains "Non-100 Expect should not emit 100 Continue" response "100 Continue"

  let count ← calls.get
  if count != 1 then
    throw <| IO.userError s!"Expected one onRequest call for non-100 Expect value, got {count}"

-- Hypothesis: Expect token should be case-insensitive.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let calls ← IO.mkRef 0
  let handler : AcceptContinueHandler := { onRequestCalls := calls }

  let raw := "POST /case HTTP/1.1\x0d\nHost: example.com\x0d\nExpect: 100-CONTINUE\x0d\nContent-Length: 5\x0d\nConnection: close\x0d\n\x0d\nhello".toUTF8
  let response ← sendRaw client server raw handler

  assertContains "Case-insensitive Expect should send 100" response "HTTP/1.1 100 Continue"
  assertContains "Case-insensitive Expect final 200" response "HTTP/1.1 200 OK"
