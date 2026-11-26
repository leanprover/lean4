import Std.Http
import Std.Http.Test.Helpers

open Std.Async
open Std Http Internal Test

/-!
Tests a response body that fails, end to end: before its head is written the client gets a 500
instead, and once the head is written the connection closes mid-response. Either way the failure is
reported once.
-/

/-- A response body that `gen` produces in the background; it fails with what `gen` throws. -/
def producer (size : Option Body.Length) (gen : Body.Stream → Async Unit) : Async Body.Stream := do
  let s ← Body.mkStream
  s.setKnownSize size
  background do
    try gen s; s.close
    catch e => try s.closeWithError e catch _ => pure ()
  return s

/-- Reads from `client` until the server closes the connection. -/
def readAll (client : Mock.Client) : Async ByteArray := do
  let mut out := ByteArray.empty
  repeat
    match ← client.recv? with
    | none => break
    | some chunk => out := out ++ chunk
  return out

/-- Serves one `GET` whose response body is `body`; returns what the client read and the reports. -/
def serve (size : Option Body.Length) (gen : Body.Stream → Async Unit) : IO (String × Array String) :=
  Async.block do
    let failures ← IO.mkRef (#[] : Array String)
    let handler : Server.StatelessHandler := {
      onRequest := fun _ => do return Response.ok.body (Body.Any.ofBody (← producer size gen))
      onFailure := fun e => failures.modify (·.push (toString e)) }
    let (client, server) ← Mock.new
    client.send (mkGet "/").toUTF8
    let serving ← async (Server.serveConnection server handler defaultConfig).run
    let out ← readAll client
    await serving
    return (String.fromUTF8! out, ← failures.get)

def check (name : String) (cond : Bool) (got : String × Array String) : IO Unit :=
  unless cond do
    throw <| IO.userError s!"{name}: got {got.1.quote} with reports {got.2}"

def boom : IO.Error := .userError "boom"

/-- A 500 that closes the connection, with no trace of the handler's response. -/
def isServerError (out : String) : Bool :=
  out.startsWith "HTTP/1.1 500 Internal Server Error\r\n" &&
    (out.splitOn "Connection: close\r\n").length == 2 && (out.splitOn "200 OK").length == 1

#eval show IO Unit from do
  let cases : List (String × Option Body.Length × (Body.Stream → Async Unit)) := [
      ("fails at once, length unknown", none, fun _ => throw boom),
      ("fails later, length unknown", none, fun _ => do sleep 30; throw boom)]
  for (name, size, gen) in cases do
    let r ← serve size gen
    check name (isServerError r.1 && r.2 == #["boom"]) r

  -- A fixed length writes the head at once, so the failure can only end the connection.
  let r ← serve (some (.fixed 5)) fun _ => do sleep 30; throw boom
  check "fixed length, fails later"
    (r.1.startsWith "HTTP/1.1 200 OK\r\n" && r.1.endsWith "Content-Length: 5\r\n\r\n" && r.2 == #["boom"]) r

  -- A chunk already written: the body ends without its last chunk, so it reads as truncated.
  let r ← serve none fun s => do s.send (Chunk.ofByteArray "hi".toUTF8); sleep 30; throw boom
  check "after a chunk"
    (r.1.startsWith "HTTP/1.1 200 OK\r\n" && r.1.endsWith "2\r\nhi\r\n" && r.2 == #["boom"]) r
