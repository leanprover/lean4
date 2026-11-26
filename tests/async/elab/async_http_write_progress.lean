import Std.Http
import Std.Http.Test.Helpers

open Std.Async
open Std Http Internal Test

/-!
Tests that `Config.writeTimeout` bounds the time without any write completing, not the time a whole
response takes: a peer that reads slowly but steadily gets a response that takes several times
`writeTimeout` in full, the keep-alive timeout counts from when a slow write completes, and a write
that ran late while nothing waited on it does not fail the connection once the peer catches up.
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

/-- A transport whose every write completes `delay` ms after it starts. -/
structure SlowWrites where
  inner : Mock.Server
  delay : Nat

instance : Transport SlowWrites where
  recv s n := Transport.recv s.inner n
  sendAll s data := do
    sleep (.ofNat s.delay)
    Transport.sendAll s.inner data
  recvSelector s n := Transport.recvSelector s.inner n
  close s := Transport.close s.inner

/-- Reads from `client` until the server closes the connection. -/
def readAll (client : Mock.Client) : Async ByteArray := do
  let mut out := ByteArray.empty
  repeat
    match ← client.recv? with
    | none => break
    | some chunk => out := out ++ chunk
  return out

/-- Reads from `client` until what it read ends with `suffix`. -/
def readUntil (client : Mock.Client) (suffix : String) : Async String := do
  let mut out := ByteArray.empty
  repeat
    match ← client.recv? with
    | none => break
    | some chunk =>
      out := out ++ chunk
      if (String.fromUTF8! out).endsWith suffix then break
  return String.fromUTF8! out

def countOccurrences (haystack needle : String) : Nat :=
  (haystack.splitOn needle).length - 1

def piece : String := String.ofList (List.replicate 1024 'x')

-- A streamed response written one slow write at a time takes about 8 × 100 ms, well past
-- `writeTimeout`, while every write completes within it. It is written in full, the pipelined
-- request behind it is served, and no failure is reported.
#eval withTimeout "slow but steady reader" 5000 <| Async.block do
  let failures ← IO.mkRef (0 : Nat)
  let handler := Server.Handler.ofFns
    (onRequest := fun req =>
      if toString req.line.uri == "/slow" then
        Response.ok |>.stream fun out => do
          for _ in [0:8] do
            out.send (Chunk.ofByteArray piece.toUTF8)
            sleep 80
      else Response.ok |>.text "after")
    (onFailure := fun _ => failures.modify (· + 1))
  let config : Config := { defaultConfig with writeTimeout := 300 }
  let (client, server) ← Mock.new
  client.send (mkGet "/slow" ++ mkGetClose "/after").toUTF8
  Std.Http.Server.serveConnection ({ inner := server, delay := 100 } : SlowWrites) handler config
    |>.run
  let response := String.fromUTF8! (← readAll client)
  unless countOccurrences response piece == 8 do
    throw (IO.userError s!"the slow response was cut short:\n{response.take 300}")
  unless response.endsWith "after" do
    throw (IO.userError s!"the pipelined request was not served:\n{response.takeEnd 300}")
  unless (← failures.get) == 0 do
    throw (IO.userError s!"{← failures.get} failures were reported for a peer that kept reading")

-- A response whose single write takes 500 ms, longer than `keepAliveTimeout` but within
-- `writeTimeout`, keeps the connection open for a request sent 100 ms after it arrives.
#eval withTimeout "keep-alive after a slow write" 5000 <| Async.block do
  let config : Config :=
    { defaultConfig with writeTimeout := 1000, keepAliveTimeout := ⟨300, by decide⟩ }
  let (client, server) ← Mock.new
  client.send (mkGet "/").toUTF8
  let conn ← async <|
    (Std.Http.Server.serveConnection ({ inner := server, delay := 500 } : SlowWrites) okHandler
      config).run
  let first ← readUntil client "ok"
  unless first.startsWith "HTTP/1.1 200" do
    throw (IO.userError s!"unexpected first response:\n{first}")
  sleep 100
  client.send (mkGetClose "/").toUTF8
  await conn
  let second := String.fromUTF8! (← readAll client)
  unless second.startsWith "HTTP/1.1 200" do
    throw (IO.userError s!"the connection closed before its keep-alive timeout:\n{second}")

/-- A transport whose first write completes after `first` ms and every later one after `rest` ms. -/
structure SlowFirst where
  inner : Mock.Server
  count : IO.Ref Nat
  first : Nat
  rest : Nat

instance : Transport SlowFirst where
  recv s n := Transport.recv s.inner n
  sendAll s data := do
    let n ← s.count.modifyGet fun n => (n, n + 1)
    sleep (.ofNat (if n == 0 then s.first else s.rest))
    Transport.sendAll s.inner data
  recvSelector s n := Transport.recvSelector s.inner n
  close s := Transport.close s.inner

-- One write takes 500 ms, past `writeTimeout`, while the connection waits only on the response
-- body, and then the peer catches up. Nothing waited on that write while it ran late, so the
-- connection goes on: the pipelined requests behind it are served and no failure is reported.
#eval withTimeout "a late write the peer caught up on" 8000 <| Async.block do
  let failures ← IO.mkRef (#[] : Array String)
  let handler := Server.Handler.ofFns
    (onRequest := fun req =>
      if toString req.line.uri == "/slow" then
        Response.ok |>.stream fun out => do
          out.send (Chunk.ofByteArray "first".toUTF8)
          sleep 800
          out.send (Chunk.ofByteArray "second".toUTF8)
      else Response.ok |>.text "after")
    (onFailure := fun e => failures.modify (·.push (toString e)))
  let config : Config := { defaultConfig with writeTimeout := 300 }
  let (client, server) ← Mock.new
  client.send (mkGet "/slow" ++ mkGet "/after" ++ mkGetClose "/after").toUTF8
  let transport : SlowFirst := { inner := server, count := ← IO.mkRef 0, first := 500, rest := 20 }
  Std.Http.Server.serveConnection transport handler config |>.run
  let response := String.fromUTF8! (← readAll client)
  unless countOccurrences response "HTTP/1.1 200" == 3 && response.endsWith "after" do
    throw (IO.userError s!"the requests after the late write were not served:\n{response}")
  unless (← failures.get).isEmpty do
    throw (IO.userError s!"failures were reported for a peer that caught up: {← failures.get}")
