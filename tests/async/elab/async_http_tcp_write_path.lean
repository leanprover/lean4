import Std.Http.Test.Helpers
import Std.Net.Addr

/-!
Write-path tests over loopback TCP: response order for pipelined requests and streamed bodies, a
reader that starts late, a write that fails, which must close the connection without running the
handler of the pipelined `POST` behind it, a stalled streamed body, a client that leaves
mid-stream, and a keep-alive timeout that must not run while the peer still reads the response.
-/

open Std.Async
open Std Http Internal Test
open Std.Net

def connectPair : Async (TCP.Socket.Client × TCP.Socket.Client) := do
  let server ← TCP.Socket.Server.mk
  server.bind (SocketAddressV4.mk (.ofParts 127 0 0 1) 0)
  server.listen 128
  let addr ← server.getSockName
  let client ← TCP.Socket.Client.mk
  client.connect addr
  let conn ← server.accept
  return (client, conn)

def readAll (client : TCP.Socket.Client) : Async ByteArray := do
  let mut out := ByteArray.empty
  repeat
    match ← client.recv? 65536 with
    | none => break
    | some c => out := out ++ c
  return out

/-- The text between each `open` and the next `close`, in order. -/
def tokens (s : String) (open_ close : String) : List String :=
  (s.splitOn open_).drop 1 |>.map fun p => (p.splitOn close).headD ""

def recordingHandler (failures : IO.Ref (Array String))
    (f : Request Body.Stream → ContextAsync (Response Body.Any)) : Server.StatelessHandler :=
  { onRequest := f, onFailure := fun e => failures.modify (·.push (toString e)) }

def withDeadline [Inhabited α] (name : String) (ms : Nat) (x : Async α) : Async α :=
  Async.race x (do sleep (.ofNat ms); throw <| IO.userError s!"{name}: no result after {ms} ms")

def config : Config := { defaultConfig with maxRequests := 1000 }

def expectNoFailures (failures : IO.Ref (Array String)) : IO Unit := do
  let fs ← failures.get
  unless fs.isEmpty do throw <| IO.userError s!"unexpected failures: {fs}"

#eval runGroup "pipelined responses keep their order" <| Async.block do
  let (client, conn) ← connectPair
  let n := 300
  let mut raw := ""
  for i in [0:n] do raw := raw ++ mkGet s!"/r{i}"
  raw := raw ++ mkGetClose s!"/r{n}"
  let failures ← IO.mkRef #[]
  let h := recordingHandler failures fun req => Response.ok |>.text s!"<{req.line.uri}>"
  let serve ← async (Server.serveConnection conn h config |>.run)
  let send ← async do client.send raw.toUTF8; client.shutdown
  let res ← withDeadline "pipelined" 20000 (readAll client)
  await send
  await serve
  assertResponseCount res (n + 1)
  let got := tokens (String.fromUTF8! res) "<" ">"
  unless got == (List.range (n + 1)).map (s!"/r{·}") do
    throw <| IO.userError s!"responses out of order: {got.take 10}"
  expectNoFailures failures

#eval runGroup "streamed chunks and the next response keep their order" <| Async.block do
  let (client, conn) ← connectPair
  let raw := mkGet "/stream" ++ mkGet "/tail" ++ mkGetClose "/tail"
  let failures ← IO.mkRef #[]
  let h := recordingHandler failures fun req =>
    if toString req.line.uri == "/stream" then
      Response.ok |>.stream fun s => do
        for i in [0:500] do
          s.send (Chunk.ofByteArray s!"[{i}]".toUTF8)
    else
      Response.ok |>.text "[tail]"
  let serve ← async (Server.serveConnection conn h config |>.run)
  let send ← async do client.send raw.toUTF8; client.shutdown
  let res ← withDeadline "streamed" 20000 (readAll client)
  await send
  await serve
  assertResponseCount res 3
  let got := tokens (String.fromUTF8! res) "[" "]"
  unless got == (List.range 500).map toString ++ ["tail", "tail"] do
    throw <| IO.userError s!"chunks out of order: {got.take 10} ... {got.drop 495}"
  expectNoFailures failures

#eval runGroup "late reader gets the whole streamed body in order" <| Async.block do
  let (client, conn) ← connectPair
  let raw := mkGetClose "/big"
  let failures ← IO.mkRef #[]
  let pad := String.ofList (List.replicate 4000 'x')
  let h := recordingHandler failures fun _ =>
    Response.ok |>.stream fun s => do
      for i in [0:1024] do
        s.send (Chunk.ofByteArray s!"<{i}>{pad}".toUTF8)
  let serve ← async (Server.serveConnection conn h config |>.run)
  let send ← async do client.send raw.toUTF8; client.shutdown
  sleep 300
  let res ← withDeadline "late reader" 20000 (readAll client)
  await send
  await serve
  let got := tokens (String.fromUTF8! res) "<" ">"
  unless got == (List.range 1024).map toString do
    throw <| IO.userError s!"chunks out of order or missing: {got.length} tokens"
  expectNoFailures failures

/-- Sends `raw` from a fresh client and drops the client, which closes it without reading. -/
def sendFromDroppedClient (raw : ByteArray) : Async TCP.Socket.Client := do
  let (client, conn) ← connectPair
  client.send raw
  return conn

#eval runGroup "failed write closes the connection before the next pipelined handler" <| Async.block do
  let conn ← sendFromDroppedClient (mkGet "/first" ++ mkPost "/second" "x" ++ mkGetClose "/third").toUTF8
  let failures ← IO.mkRef #[]
  let later ← IO.mkRef #[]
  let big := ByteArray.mk (Array.replicate (8 * 1024 * 1024) 'x'.toUInt8)
  let h := recordingHandler failures fun req => do
    let uri := toString req.line.uri
    if uri == "/first" then
      -- Let the client's close reach the server before writing.
      sleep 200
      Response.ok |>.bytes big
    else
      later.modify (·.push uri)
      Response.ok |>.text "later"
  withDeadline "failed write" 20000 (Server.serveConnection conn h config |>.run)
  let ran ← later.get
  unless ran.isEmpty do
    throw <| IO.userError s!"handlers ran after a failed write: {ran}"
  if (← failures.get).isEmpty then
    throw <| IO.userError "the failed write was not reported"

#eval runGroup "stalled streamed body still times out" <| Async.block do
  let (client, conn) ← connectPair
  let failures ← IO.mkRef #[]
  let h := recordingHandler failures fun _ =>
    Response.ok |>.stream fun s => do
      s.send (Chunk.ofByteArray "[first]".toUTF8)
      sleep 5000
      s.send (Chunk.ofByteArray "[late]".toUTF8)
  let cfg := { config with lingeringTimeout := 300 }
  let serve ← async (Server.serveConnection conn h cfg |>.run)
  client.send (mkGet "/stall").toUTF8
  let start ← IO.monoMsNow
  withDeadline "stalled stream" 3000 (await serve)
  let elapsed := (← IO.monoMsNow) - start
  unless elapsed < 3000 do throw <| IO.userError s!"took {elapsed} ms"
  let res ← withDeadline "stalled read" 3000 (readAll client)
  assertContains res "[first]"
  assertAbsent res "[late]"

#eval runGroup "client that leaves mid-stream ends the connection" <| Async.block do
  let failures ← IO.mkRef #[]
  let h := recordingHandler failures fun _ =>
    Response.ok |>.stream fun s => do
      for i in [0:200] do
        s.send (Chunk.ofByteArray s!"[{i}]".toUTF8)
        sleep 20
  let server ← TCP.Socket.Server.mk
  server.bind (SocketAddressV4.mk (.ofParts 127 0 0 1) 0)
  server.listen 128
  let addr ← server.getSockName
  let serve ← async do
    let conn ← server.accept
    Server.serveConnection conn h config |>.run
  let drop : Async Unit := do
    let client ← TCP.Socket.Client.mk
    client.connect addr
    client.send (mkGet "/slow").toUTF8
    discard <| client.recv? 65536
  drop
  let start ← IO.monoMsNow
  withDeadline "client left" 3000 (await serve)
  let elapsed := (← IO.monoMsNow) - start
  unless elapsed < 3000 do throw <| IO.userError s!"took {elapsed} ms"
  if (← failures.get).isEmpty then
    throw <| IO.userError "the lost client was not reported"

/-- Reads one response whose body is `size` bytes long. -/
def readResponse (client : TCP.Socket.Client) (size : Nat) : Async ByteArray := do
  let mut out := ByteArray.empty
  repeat
    if out.size ≥ 512 then
      let head := (String.fromUTF8! (out.extract 0 512)).splitOn "\x0d\n\x0d\n" |>.headD ""
      if out.size ≥ head.utf8ByteSize + 4 + size then break
    match ← client.recv? 65536 with
    | none => break
    | some c => out := out ++ c
  return out

/--
A socket whose writes of at least `gateBytes` bytes complete only once `gate` is resolved. A write
completes once the kernel takes the bytes, so whether a large write is still in flight when the
peer stops reading depends on the platform's socket buffers; the gate makes it the test's choice.
-/
structure GatedSocket where
  socket : TCP.Socket.Client
  gateBytes : Nat
  /-- Resolved once a gated write starts. -/
  started : IO.Promise Unit
  gate : IO.Promise Unit

def GatedSocket.new (socket : TCP.Socket.Client) (gateBytes : Nat) : BaseIO GatedSocket :=
  return { socket, gateBytes, started := ← IO.Promise.new, gate := ← IO.Promise.new }

instance : Transport GatedSocket where
  recv s expect := Transport.recv s.socket expect
  sendAll s data := do
    let gated := data.foldl (· + ·.size) 0 ≥ s.gateBytes
    if gated then s.started.resolve ()
    Transport.sendAll s.socket data
    if gated then discard <| Async.ofTask s.gate.result?
  recvSelector s expect := Transport.recvSelector s.socket expect
  close s := Transport.close s.socket

#eval runGroup "keep-alive timeout starts once the response is written" <| Async.block do
  let (client, conn) ← connectPair
  let failures ← IO.mkRef #[]
  let size := 1024 * 1024
  let big := ByteArray.mk (Array.replicate size 'x'.toUInt8)
  let h := recordingHandler failures fun req =>
    if toString req.line.uri == "/big" then Response.ok |>.bytes big else Response.ok |>.text "[next]"
  let cfg := { config with keepAliveTimeout := ⟨300, by decide⟩ }
  let socket ← GatedSocket.new conn size
  let serve ← async (Server.serveConnection socket h cfg |>.run)
  client.send (mkGet "/big").toUTF8
  -- The keep-alive timeout passes while the body's write is in flight.
  sleep 1000
  let first ← withDeadline "slow reader" 20000 (readResponse client size)
  assertStatus first "HTTP/1.1 200"
  -- The write completes only now, so the keep-alive timeout starts over from here.
  socket.gate.resolve ()
  client.send (mkGetClose "/next").toUTF8
  let second ← withDeadline "second response" 5000 (readAll client)
  await serve
  assertContains second "[next]"
  expectNoFailures failures

#eval runGroup "keep-alive timeout runs from when the write completes" <| Async.block do
  let (client, conn) ← connectPair
  let failures ← IO.mkRef #[]
  let size := 64 * 1024
  let big := ByteArray.mk (Array.replicate size 'x'.toUInt8)
  let h := recordingHandler failures fun req =>
    if toString req.line.uri == "/big" then Response.ok |>.bytes big else Response.ok |>.text "[next]"
  let cfg := { config with keepAliveTimeout := ⟨300, by decide⟩ }
  let socket ← GatedSocket.new conn size
  let serve ← async (Server.serveConnection socket h cfg |>.run)
  client.send (mkGet "/big").toUTF8
  discard <| Async.ofTask socket.started.result?
  -- The write completes shortly before a timeout counted from the hand-over would run out.
  sleep 250
  socket.gate.resolve ()
  sleep 100
  client.send (mkGetClose "/next").toUTF8
  let res ← withDeadline "responses" 5000 (readAll client)
  await serve
  assertStatus res "HTTP/1.1 200"
  assertContains res "[next]"
  expectNoFailures failures
