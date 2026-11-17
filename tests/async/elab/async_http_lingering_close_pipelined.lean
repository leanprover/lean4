import Std.Http
import Std.Http.Test.Helpers

open Std.Async
open Std Http Internal Test

/-!
Tests the lingering close (RFC 9112 §9.6) when the server ends a keep-alive connection while the
client pipelines. The client sends `GET /b` while the handler of `GET /a` runs, and the connection does
not read while a handler runs, so `GET /b` still waits in the transport when the server decides to
close: the handler answers `Connection: close`, `/a` is the last request `maxRequests` allows, or the
handler fails and the server answers `500`. Closing a TCP socket with unread input sends a reset, which
can destroy the response before the client reads it, so the server has to shut down its write side
first and read until the client closes. The transport here records whether it did.
-/

/-- An in-memory transport that records a shutdown, and a close while input was still unread. -/
structure Pipe where
  toServer : Std.CloseableChannel ByteArray
  toClient : Std.CloseableChannel ByteArray
  shut : IO.Ref Bool
  closed : IO.Ref Bool
  closedUnread : IO.Ref Bool

def closeChannel (channel : Std.CloseableChannel ByteArray) : BaseIO Unit := do
  unless ← channel.isClosed do
    discard <| EIO.toBaseIO channel.close

instance : Transport Pipe where
  recv pipe _ := do await (← pipe.toServer.recv)
  sendAll pipe data := do
    for chunk in data do
      Async.ofAsyncTask ((← pipe.toClient.send chunk) |>.map (Except.mapError (IO.userError ∘ toString)))
  recvSelector pipe _ := pipe.toServer.recvSelector
  close pipe := do
    if !(← pipe.shut.get) && (← pipe.toServer.tryRecv).isSome then
      pipe.closedUnread.set true
    pipe.closed.set true
    closeChannel pipe.toServer
    closeChannel pipe.toClient
  shutdown pipe := do
    pipe.shut.set true
    closeChannel pipe.toClient
    return true

partial def drain (channel : Std.CloseableChannel ByteArray) (acc : ByteArray := .empty) : BaseIO ByteArray := do
  match ← channel.tryRecv with
  | some bytes => drain channel (acc ++ bytes)
  | none => return acc

/--
Sends `GET /a`, then `GET /b` once the handler of `/a` runs, and lets the handler answer with `answer`.
The server must answer `/a` with `status`, say `close`, not answer `/b`, and shut down its write side
before it closes.
-/
def checkPipelinedClose (name : String) (config : Config) (answer : Async (Response Body.Any))
    (status : String) : IO Unit := Async.block do
  let pipe : Pipe := {
    toServer := ← Std.CloseableChannel.new, toClient := ← Std.CloseableChannel.new,
    shut := ← IO.mkRef false, closed := ← IO.mkRef false, closedUnread := ← IO.mkRef false }
  let started : IO.Promise Unit ← IO.Promise.new
  let proceed : IO.Promise Unit ← IO.Promise.new
  let handler := Server.Handler.ofFn fun req => do
    if toString req.line.uri == "/a" then
      started.resolve ()
      discard <| await proceed.result?
    answer
  let serving ← async (t := AsyncTask) (ContextAsync.run (Server.serveConnection pipe handler config))
  discard <| pipe.toServer.send (mkGet "/a").toUTF8
  discard <| await started.result?
  discard <| pipe.toServer.send (mkGet "/b").toUTF8
  proceed.resolve ()
  let mut waited := 0
  while !(← pipe.shut.get) && !(← pipe.closed.get) && waited < 5000 do
    sleep 1
    waited := waited + 1
  let shut ← pipe.shut.get
  let closedUnread ← pipe.closedUnread.get
  let output ← drain pipe.toClient
  -- The client closes its side, which ends the server's lingering read.
  closeChannel pipe.toServer
  discard <| await serving
  let text := String.fromUTF8! output
  unless text.startsWith status && text.contains "Connection: close" &&
      (text.splitOn "HTTP/1.1 ").length == 2 && shut && !closedUnread do
    throw <| IO.userError
      s!"'{name}': expected one {status.quote} with close, then a shutdown before the close; got shutdown {shut}, closed with unread input {closedUnread}, output {(text.take 300).toString.quote}"

def runCases (cases : List (IO Unit)) : IO Unit := do
  let mut errors : Array String := #[]
  for c in cases do
    try c catch e => errors := errors.push (toString e)
  unless errors.isEmpty do throw (IO.userError ("\n".intercalate errors.toList))

#eval runCases [
  checkPipelinedClose "Connection: close from the handler"
    { defaultConfig with lingeringTimeout := 3000 }
    (do return ← Response.ok |>.header! "Connection" "close" |>.empty) "HTTP/1.1 200",
  checkPipelinedClose "maxRequests reached"
    { defaultConfig with lingeringTimeout := 3000, maxRequests := 1 }
    (do return ← Response.ok |>.empty) "HTTP/1.1 200",
  checkPipelinedClose "the handler fails"
    { defaultConfig with lingeringTimeout := 3000 }
    (throw (IO.userError "handler failed")) "HTTP/1.1 500",
  checkPipelinedClose "a 1 MiB answer with Connection: close"
    { defaultConfig with lingeringTimeout := 3000 }
    (do return ← Response.ok |>.header! "Connection" "close" |>.bytes (ByteArray.mk (Array.replicate 1048576 120)))
    "HTTP/1.1 200"]
