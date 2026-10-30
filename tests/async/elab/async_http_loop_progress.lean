import Std.Http.Test.Helpers
import Std.Async.Process
import Std.Net.Addr

open Std.Async
open Std Http Internal Test
open Std.Net

/-!
While a handler runs, the connection loop still has work of its own: delivering a request body that
is still arriving, sending `100 Continue`, writing the responses to earlier pipelined requests, and
finishing a response before the keep-alive timeout starts. These tests check that a handler that
suspends, blocks its thread or closes its body unread does not stop that work. The server is started
before the input arrives, so the loop is already waiting and runs handlers inline.
-/

/-- Waits up to `ms` milliseconds for `task`, returning `none` on timeout. -/
def waitFor (task : Task α) (ms : Nat) : IO (Option α) := do
  for _ in [0:ms / 5] do
    if ← IO.hasFinished task then return some task.get
    IO.sleep 5
  if ← IO.hasFinished task then return some task.get
  return none

/-- Suspends the handler for a few milliseconds. -/
def pause : ContextAsync Unit := do
  let _ ← Selectable.one #[.case (← Selector.sleep 10) pure]

/-- The bodies of the responses in `response`, in order. -/
def bodies (response : ByteArray) : List String :=
  (String.fromUTF8! response).splitOn "HTTP/1.1 " |>.drop 1 |>.map fun part =>
    (part.splitOn "\x0d\n\x0d\n").getD 1 ""

def assertBodies (name : String) (response : ByteArray) (expected : List String) : IO Unit := do
  let got := bodies response
  unless got == expected do
    throw <| IO.userError
      s!"{name}: expected bodies {expected}, got {got}:\n{(String.fromUTF8! response).quote}"

/-- Receives from `client` until the text received so far satisfies `done`, or the server closes. -/
partial def recvUntil (client : Mock.Client) (done : String → Bool) (acc : ByteArray := .empty) :
    Async ByteArray := do
  if done (String.fromUTF8! acc) then return acc
  match ← client.recv? with
  | some chunk => recvUntil client done (acc ++ chunk)
  | none => return acc

/-- A POST head ending the connection after its response, with the header lines `extra`. -/
def postHead (extra : String) : String :=
  s!"POST / HTTP/1.1\x0d\nHost: example.com\x0d\n{extra}Connection: close\x0d\n\x0d\n"

/--
Serves one mock connection whose input arrives as `parts`, each `gap` milliseconds after the
previous one, and returns everything the server wrote. A connection still running after `ms`
milliseconds is cancelled and reported as stuck.
-/
def serveParts (name : String) (parts : List String) (handler : TestHandler)
    (config : Config := defaultConfig) (gap : UInt32 := 20) (ms : Nat := 3000) : IO ByteArray := do
  let (client, server) ← Mock.new
  let ctx ← CancellationContext.new
  let conn ← EAsync.toBaseIO (ε := IO.Error) <|
    Std.Http.Server.serveConnection server handler config |>.runIn ctx
  for part in parts do
    IO.sleep gap
    Async.block (client.send part.toUTF8)
  let some result ← waitFor conn ms
    | ctx.cancel .shutdown
      discard <| waitFor conn 1000
      let written := (← client.tryRecv?).getD .empty
      throw <| IO.userError
        s!"{name}: the connection was stuck for {ms} ms after writing {(String.fromUTF8! written).quote}"
  IO.ofExcept result
  return (← client.tryRecv?).getD .empty

#eval runGroup "Body still arriving when a suspending handler starts" do
  let readLate : TestHandler := fun req => do
    pause
    Response.ok |>.text (← req.body.readAll)

  let name := "rest of a fixed-length body"
  let r ← serveParts name [postHead "Content-Length: 10\x0d\n" ++ "hello", "world"] readLate
  assertBodies name r ["helloworld"]

  let name := "fixed-length body after the head"
  let r ← serveParts name [postHead "Content-Length: 5\x0d\n", "hello"] readLate
  assertBodies name r ["hello"]

  let readChunksLate : TestHandler := fun req => do
    let mut out := ""
    for chunk in req.body do
      pause
      out := out ++ String.fromUTF8! chunk.data
    Response.ok |>.text out

  let name := "chunked body read chunk by chunk"
  let r ← serveParts name
    [postHead "Transfer-Encoding: chunked\x0d\n" ++ chunk "hello", chunk "world" ++ chunkEnd]
    readChunksLate
  assertBodies name r ["helloworld"]

/--
Sends a request head with `Expect: 100-continue`, then sends the body only once `100 Continue`
arrived, as a client that waits for the interim response does.
-/
def expectContinue (name : String) (handler : TestHandler) (ms : Nat := 500) : IO Unit := do
  let (client, server) ← Mock.new
  let ctx ← CancellationContext.new
  let conn ← EAsync.toBaseIO (ε := IO.Error) <|
    Std.Http.Server.serveConnection server handler defaultConfig |>.runIn ctx
  try
    IO.sleep 20
    Async.block <| client.send (postHead "Content-Length: 5\x0d\nExpect: 100-continue\x0d\n").toUTF8
    let interim ← EAsync.toBaseIO (ε := IO.Error) (recvUntil client (·.endsWith "\x0d\n\x0d\n"))
    let some interim ← waitFor interim ms
      | throw <| IO.userError s!"{name}: no interim response within {ms} ms"
    let interim := String.fromUTF8! (← IO.ofExcept interim)
    unless interim == "HTTP/1.1 100 Continue\x0d\n\x0d\n" do
      throw <| IO.userError s!"{name}: expected only 100 Continue before the body, got {interim.quote}"
    Async.block <| client.send "hello".toUTF8
    let some result ← waitFor conn 3000
      | throw <| IO.userError s!"{name}: the connection was stuck after the body was sent"
    IO.ofExcept result
    assertBodies name ((← client.tryRecv?).getD .empty) ["hello"]
  finally
    ctx.cancel .shutdown

#eval runGroup "Expect: 100-continue with a client that waits for it" do
  expectContinue "handler reading at once" echoHandler
  expectContinue "handler suspending before it reads" fun req => do
    pause
    Response.ok |>.text (← req.body.readAll)

#eval runGroup "Handler blocking its thread on its own body" do
  -- The wait is bounded, so a deadlock is answered instead of hanging the test.
  let blockOnBody : TestHandler := fun req => do
    let body ← EAsync.toBaseIO (ε := IO.Error) (req.body.readAll : Async String)
    let some body ← waitFor body 1500
      | Response.ok |>.text "deadlocked"
    Response.ok |>.text (← IO.ofExcept body)

  let name := "fixed-length body split across reads"
  let r ← serveParts name [postHead "Content-Length: 10\x0d\n" ++ "hello", "world"] blockOnBody
  assertBodies name r ["helloworld"]

  let name := "chunked body split across reads"
  let r ← serveParts name
    [postHead "Transfer-Encoding: chunked\x0d\n" ++ chunk "hello", chunk "world" ++ chunkEnd]
    blockOnBody
  assertBodies name r ["helloworld"]

#eval runGroup "Pipelined response while a later handler blocks its thread" do
  let name := "response to the first of two pipelined requests"
  let handler : TestHandler := fun req => do
    if toString req.line.uri == "/block" then
      IO.sleep 500
    Response.ok |>.text (toString req.line.uri)
  let (client, server) ← Mock.new
  let ctx ← CancellationContext.new
  let conn ← EAsync.toBaseIO (ε := IO.Error) <|
    Std.Http.Server.serveConnection server handler defaultConfig |>.runIn ctx
  try
    IO.sleep 20
    Async.block <| client.send (mkGet "/fast" ++ mkGetClose "/block").toUTF8
    let start ← IO.monoMsNow
    let first ← EAsync.toBaseIO (ε := IO.Error) (recvUntil client (·.contains "\x0d\n\x0d\n/fast"))
    let some first ← waitFor first 2000
      | throw <| IO.userError s!"{name}: nothing was written within 2000 ms"
    let elapsed := (← IO.monoMsNow) - start
    let first ← IO.ofExcept first
    unless (bodies first).head? == some "/fast" do
      throw <| IO.userError s!"{name}: expected the /fast response first, got {(String.fromUTF8! first).quote}"
    unless elapsed < 250 do
      throw <| IO.userError s!"{name}: written after {elapsed} ms, behind the blocked handler"
    let some result ← waitFor conn 3000
      | throw <| IO.userError s!"{name}: the connection was stuck after the second response"
    IO.ofExcept result
  finally
    ctx.cancel .shutdown

#eval runGroup "Request body closed unread while chunks are buffered" do
  let name := "chunked body over the limit closed by its handler"
  -- The second chunk is over the limit, so only the first one is handed to the stream up front.
  let closeUnread : TestHandler := fun req => do
    req.body.close
    let _ ← Selectable.one #[.case (← Selector.sleep 300) pure]
    Response.ok |>.text "closed"
  let before ← Std.IO.Process.getResourceUsage
  let r ← serveParts name
    [postHead "Transfer-Encoding: chunked\x0d\n" ++ chunk "hello" ++ chunk "world" ++ chunkEnd]
    closeUnread (config := { defaultConfig with maxBodySize := 8 })
  let after ← Std.IO.Process.getResourceUsage
  assertBodies name r ["closed"]
  let cpu (u : Std.IO.Process.ResourceUsageStats) := u.cpuUserTime.toInt + u.cpuSystemTime.toInt
  let used := cpu after - cpu before
  unless used < 150 do
    throw <| IO.userError s!"{name}: the connection used {used} ms of CPU while the handler slept 300 ms"

/-- Reads and discards `n` bytes from `client`. -/
partial def skipBytes (client : TCP.Socket.Client) (n : Nat) : Async Unit := do
  if n == 0 then return
  match ← client.recv? (min n 65536).toUInt64 with
  | some chunk => skipBytes client (n - min n chunk.size)
  | none => throw <| IO.userError s!"the connection closed with {n} bytes of the response unread"

/-- Reads from `client` until the peer closes the connection. -/
partial def readToEnd (client : TCP.Socket.Client) (acc : ByteArray := .empty) : Async ByteArray := do
  match ← client.recv? 4096 with
  | some chunk => readToEnd client (acc ++ chunk)
  | none => return acc

-- The keep-alive timeout counts from when the response is written, not from when it is queued.
#eval show IO Unit from do
  let name := "request after a response read slowly"
  let size := 32 * 1024 * 1024
  let big := "".pushn 'x' size
  let handler : TestHandler := fun req => do
    if toString req.line.uri == "/big" then Response.ok |>.text big
    else Response.ok |>.text "next"
  let config := { defaultConfig with keepAliveTimeout := ⟨300, by decide⟩ }

  let (client, conn) ← Async.block do
    let server ← TCP.Socket.Server.mk
    server.bind (SocketAddressV4.mk (.ofParts 127 0 0 1) 0)
    server.listen 1
    let client ← TCP.Socket.Client.mk
    client.connect (← server.getSockName)
    pure (client, ← server.accept)

  let ctx ← CancellationContext.new
  let serve ← EAsync.toBaseIO (ε := IO.Error) <|
    Std.Http.Server.serveConnection conn handler config |>.runIn ctx
  try
    Async.block <| client.send (mkGet "/big").toUTF8
    -- The response does not fit in the socket buffers, so it is still being written meanwhile.
    IO.sleep 800
    let exchange ← EAsync.toBaseIO (ε := IO.Error) do
      let some first ← client.recv? 65536
        | throw <| IO.userError "the connection closed before the first response"
      let head := ((String.fromUTF8! first).splitOn "\x0d\n\x0d\n").head!
      skipBytes client (head.utf8ByteSize + 4 + size - first.size)
      client.send (mkGetClose "/next").toUTF8
      readToEnd client
    let some second ← waitFor exchange 5000
      | throw <| IO.userError s!"{name}: no answer to the second request within 5000 ms"
    match second with
    | .error e => throw <| IO.userError s!"{name}: the second request failed: {e}"
    | .ok second => assertBodies name second ["next"]
    let some result ← waitFor serve 3000
      | throw <| IO.userError s!"{name}: the connection was stuck after the second response"
    IO.ofExcept result
  finally
    ctx.cancel .shutdown
