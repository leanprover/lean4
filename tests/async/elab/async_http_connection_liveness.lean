import Std.Http
import Std.Http.Test.Helpers
import Std.Net.Addr

open Std.Async
open Std Http Internal Test
open Std.Net

/-!
Tests that a connection always ends and never spins:

* a peer that stops reading cannot hold its connection, its socket, its `maxConnections` permit, or
  server shutdown past `Config.writeTimeout`;
* after the client half-closes, the loop stops polling the socket while a response streams.
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

/-- A transport whose writes never complete, as with a peer that does not read. -/
structure StalledWrites where
  inner : Mock.Server
  /-- Never resolved. Held here so that dropping it cannot complete the writes. -/
  gate : IO.Promise Unit

instance : Transport StalledWrites where
  sendAll s _ := discard <| Async.ofTask s.gate.result?
  recvSelector s n := Transport.recvSelector s.inner n
  close s := Transport.close s.inner

def stalledConfig : Config :=
  { defaultConfig with writeTimeout := 300, keepAliveTimeout := ⟨300, by decide⟩ }

/-- Serves `raw` over a transport whose writes never complete; the connection must still end. -/
def expectEnds (name : String) (raw : String) (handler : TestHandler) : IO Unit := do
  withTimeout name 3000 <| Async.block do
    let (client, server) ← Mock.new
    let gate ← IO.Promise.new
    client.send raw.toUTF8
    Std.Http.Server.serveConnection ({ inner := server, gate } : StalledWrites) handler stalledConfig |>.run
    gate.resolve ()

def bigBody : ByteArray := ByteArray.mk (Array.replicate (256 * 1024) 'x'.toUInt8)

#eval expectEnds "stalled response, Connection: close" (mkGetClose "/") okHandler
#eval expectEnds "stalled response, keep-alive" (mkGet "/") okHandler
#eval expectEnds "stalled streamed response over the queue limit" (mkGetClose "/") fun _ =>
  Response.ok |>.stream fun out => do
    for _ in [0:8] do
      out.send (Chunk.ofByteArray bigBody)
#eval expectEnds "stalled response before a pipelined unsafe request"
  (mkGet "/" ++ mkPost "/" "body" "Connection: close\x0d\n") okHandler

def readAll (client : TCP.Socket.Client) : Async ByteArray := do
  let mut out := ByteArray.empty
  repeat
    match ← client.recv? 65536 with
    | none => break
    | some chunk => out := out ++ chunk
  return out

def within (ms : Nat) (action : Async Unit) : Async Bool :=
  Async.race (do action; pure true) (do sleep (.ofNat ms); pure false)

-- Over TCP, a peer that requests a large response and never reads it gives up its connection
-- permit, so the next client is served, and shutdown completes. The response is streamed in pieces:
-- Windows accepts a whole write, however large, while its send buffer has room, so a single write
-- would never stall.
#eval withTimeout "non-reading TCP peer" 20000 <| Async.block do
  let pieces := 128
  let handler : TestHandler := fun req =>
    if toString req.line.uri == "/big" then
      Response.ok |>.stream fun out => do
        for _ in [0:pieces] do
          out.send (Chunk.ofByteArray bigBody)
    else Response.ok |>.text "small"
  let config : Config := { stalledConfig with maxConnections := 1 }
  let server ← Server.serve (SocketAddressV4.mk (.ofParts 127 0 0 1) 0) handler config
  let some addr := server.localAddr | throw (IO.userError "the server has no address")
  let stalled ← TCP.Socket.Client.mk
  stalled.connect addr
  stalled.send (mkGetClose "/big").toUTF8
  sleep 200
  let good ← TCP.Socket.Client.mk
  let response ← IO.mkRef ByteArray.empty
  let served ← within 5000 do
    good.connect addr
    good.send (mkGetClose "/small").toUTF8
    response.set (← readAll good)
  unless served && (String.fromUTF8! (← response.get)).startsWith "HTTP/1.1 200 OK" do
    throw (IO.userError "the second client was not served while the first one did not read")
  unless ← within 5000 server.shutdownAndWait do
    throw (IO.userError "shutdown did not complete while a peer did not read")
  -- The server closed the stalled socket rather than leaving the write pending, so the peer gets
  -- only what the kernel had buffered before the connection ends.
  let mut received := 0
  repeat
    match ← (try stalled.recv? 65536 catch _ => pure none) with
    | some chunk => received := received + chunk.size
    | none => break
  unless received < pieces * bigBody.size do
    throw (IO.userError s!"the abandoned response was still written in full ({received} bytes)")

/-- A transport that counts how often the connection polls the socket for input. -/
structure CountingPolls where
  inner : Mock.Server
  polls : IO.Ref Nat

instance : Transport CountingPolls where
  sendAll s data := Transport.sendAll s.inner data
  recvSelector s n :=
    let selector := Transport.recvSelector s.inner n
    { tryFn := do
        s.polls.modify (· + 1)
        selector.tryFn
      registerFn := selector.registerFn
      unregisterFn := selector.unregisterFn }
  close s := Transport.close s.inner

-- After the client half-closes, the response keeps streaming without the loop polling the socket
-- in a busy loop.
#eval withTimeout "half-closed client" 10000 <| Async.block do
  let handler : TestHandler := fun _ =>
    Response.ok |>.stream fun out => do
      for i in [0:3] do
        out.send (Chunk.ofByteArray s!"[{i}]".toUTF8)
        sleep 200
  let (client, server) ← Mock.new
  let transport : CountingPolls := { inner := server, polls := ← IO.mkRef 0 }
  client.send (mkGetClose "/").toUTF8
  client.getSendChan.close
  Std.Http.Server.serveConnection transport handler defaultConfig |>.run
  let mut out := ""
  repeat
    match ← client.tryRecv? with
    | some bytes => out := out ++ String.fromUTF8! bytes
    | none => break
  unless out.contains "[2]" do
    throw (IO.userError s!"the streamed response was cut short: {out.quote}")
  let polls ← transport.polls.get
  unless polls < 50 do
    throw (IO.userError s!"the connection polled the socket {polls} times after the client half-closed")
