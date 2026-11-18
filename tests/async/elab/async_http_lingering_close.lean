import Std.Http
import Std.Http.Test.Helpers
import Std.Net.Addr

open Std.Async
open Std Http Internal Test
open Std.Net

/-!
Tests the lingering close (RFC 9112 §9.6). When the server answers before the end of an upload, with
`413` to an upload far over `maxBodySize` or with `417` to `Expect: 100-continue` whose client sends
its body at once, the client is still sending. The server shuts down its write side and drains the
input before closing, so the client neither gets a reset on its sends nor loses the response. This
holds as well when the server rejects a head before any of the body arrives, so it has no unread
input when it closes, and whenever it ends the connection after an exchange while the client has
pipelined another request: for `Connection: close` from the client or the handler, an HTTP/1.0
request, `maxRequests`, or `500` when the handler fails.
-/

def withTimeout {α : Type} (name : String) (ms : Nat) (action : IO α) : IO α := do
  let task ← IO.asTask action
  let rec loop : Nat → IO α
    | 0 => do
      IO.cancel task
      throw <| IO.userError s!"'{name}' did not finish within {ms} ms"
    | n + 1 => do
      if (← IO.getTaskState task) == .finished then
        match ← IO.wait task with
        | .ok x => pure x
        | .error e => throw e
      else
        IO.sleep 10
        loop n
  loop ((ms + 9) / 10)

/--
Uploads 4 MiB with the request head `extra` adds fields to, and checks that the response starts with
`status` and that neither the sends nor the receives saw a reset. With `awaitResponse`, the client
receives the start of the response before it sends the body, so the server answers from the head
alone.
-/
def checkLingers [Server.Handler σ] (name : String) (handler : σ) (config : Config) (extra : String)
    (status : String) (awaitResponse : Bool := false) : IO Unit :=
  withTimeout name 20000 <| Async.block do
    let server ← Server.serve (SocketAddressV4.mk (.ofParts 127 0 0 1) 0) handler config
    let some addr := server.localAddr | throw (IO.userError "the server has no address")
    let client ← TCP.Socket.Client.mk
    client.connect addr
    let pieces := 64
    let piece := ByteArray.mk (Array.replicate 65536 'x'.toUInt8)
    client.send
      s!"POST / HTTP/1.1\x0d\nHost: a\x0d\n{extra}Content-Length: {pieces * piece.size}\x0d\n\x0d\n".toUTF8
    let mut response := ByteArray.empty
    let mut recvError : Option String := none
    if awaitResponse then
      try
        if let some bytes ← client.recv? 65536 then
          response := bytes
      catch e =>
        recvError := some (toString e)
    let mut sendError : Option String := none
    for _ in [0:pieces] do
      try client.send piece
      catch e =>
        sendError := some (toString e)
        break
    repeat
      try
        match ← client.recv? 65536 with
        | none => break
        | some bytes => response := response ++ bytes
      catch e =>
        recvError := some (toString e)
        break
    server.shutdownAndWait
    let text := String.fromUTF8! response
    unless text.startsWith status && sendError.isNone && recvError.isNone do
      throw <| IO.userError
        s!"'{name}': expected {status.quote} and no reset, got {(text.take 40).toString.quote}, send error {sendError}, receive error {recvError}"

#eval checkLingers "lingering close after 413" okHandler
  { defaultConfig with maxBodySize := 1024, lingeringTimeout := 3000 } "" "HTTP/1.1 413"

-- The client sends its body without waiting for `100 Continue`.
#eval checkLingers "lingering close after 417"
  (Server.Handler.ofFns (fun _ => Response.ok |>.text "ok") (onContinue := fun _ => pure false))
  { defaultConfig with lingeringTimeout := 3000 } "Expect: 100-continue\x0d\n" "HTTP/1.1 417"

#eval checkLingers "lingering close after 413 to a head alone" okHandler
  { defaultConfig with maxBodySize := 1024, lingeringTimeout := 3000 } "" "HTTP/1.1 413"
  (awaitResponse := true)

-- Two different `Content-Length` values make the head invalid (RFC 9112 §6.3).
#eval checkLingers "lingering close after 400 to a head alone" okHandler
  { defaultConfig with lingeringTimeout := 3000 } "Content-Length: 1\x0d\n" "HTTP/1.1 400"
  (awaitResponse := true)

/-- A `Mock.Server` that can shut down its write side, and records whether it did so (`true`) or
closed (`false`) first. -/
structure Recorded where
  server : Mock.Server
  shutFirst : IO.Ref (Option Bool)

instance : Transport Recorded where
  recv t n := Transport.recv t.server n
  sendAll t data := Transport.sendAll t.server data
  recvSelector t n := Transport.recvSelector t.server n
  close t := do
    t.shutFirst.modify (· <|> some false)
    t.server.close
  shutdown t := do
    t.shutFirst.modify (· <|> some true)
    t.server.getSendChan.close
    return true

/--
Sends `GET /b` while the handler of `first`, a request for `/a`, runs. The connection does not read
while a handler runs, so `/b` is still unread when the connection ends after `answer`: the server
must answer `/a` alone with `status` and shut down its write side before it closes.
-/
def checkPipelined (name : String) (answer : ContextAsync (Response Body.Any)) (status : String)
    (first : String := mkGet "/a") (config : Config := { defaultConfig with lingeringTimeout := 3000 }) :
    IO Unit :=
  withTimeout name 20000 <| Async.block do
    let (client, server) ← Mock.new
    let shutFirst ← IO.mkRef (none : Option Bool)
    let started : IO.Promise Unit ← IO.Promise.new
    let proceed : IO.Promise Unit ← IO.Promise.new
    let handler := Server.Handler.ofFn fun req => do
      if toString req.line.uri == "/a" then
        started.resolve ()
        discard <| await proceed.result?
      answer
    let serving ← async (t := AsyncTask) (ContextAsync.run (Server.serveConnection
      ({ server, shutFirst } : Recorded) handler config))
    client.send first.toUTF8
    discard <| await started.result?
    client.send (mkGet "/b").toUTF8
    proceed.resolve ()
    let mut waited := 0
    while (← shutFirst.get).isNone && waited < 5000 do
      sleep 1
      waited := waited + 1
    let text := String.fromUTF8! ((← client.tryRecv?).getD .empty)
    -- The client closes, which ends the server's lingering read.
    client.close
    discard <| await serving
    let shutFirst ← shutFirst.get
    unless text.startsWith status && text.contains "Connection: close" &&
        (text.splitOn "HTTP/1.1 ").length == 2 && shutFirst == some true do
      throw <| IO.userError
        s!"'{name}': expected one {status.quote} with close, then a shutdown before the close; got shut down first {shutFirst}, output {(text.take 200).toString.quote}"

#eval checkPipelined "Connection: close from the handler with a pipelined request"
  (do return ← Response.ok |>.header! "Connection" "close" |>.empty) "HTTP/1.1 200"

#eval checkPipelined "500 with a pipelined request" (throw (IO.userError "handler failed"))
  "HTTP/1.1 500"

-- The connection ends after this exchange whoever asked for it, so `/b` is unread in each case.
#eval checkPipelined "Connection: close from the client with a pipelined request"
  (Response.ok |>.text "a") "HTTP/1.1 200" (first := mkGetClose "/a")

#eval checkPipelined "an HTTP/1.0 request with a pipelined request"
  (Response.ok |>.text "a") "HTTP/1.1 200" (first := "GET /a HTTP/1.0\x0d\n\x0d\n")

#eval checkPipelined "maxRequests 1 with a pipelined request"
  (Response.ok |>.text "a") "HTTP/1.1 200"
  (config := { defaultConfig with lingeringTimeout := 3000, maxRequests := 1 })
