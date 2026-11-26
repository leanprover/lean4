import Std.Http
import Std.Http.Test.Helpers

open Std.Async
open Std Http Internal Test

/-!
Tests a response body of unknown length that fails before producing anything, for a request after
which the connection closes (HTTP/1.0, or `Connection: close`). As with keep-alive, the client must
get a 500 instead of the handler's response: a head written before any body byte would leave an
HTTP/1.0 client with a close-delimited body that reads as complete and empty. A body that does
produce its bytes is still written in full.
-/

/-- A response body of unknown length that fails after `ms` without producing anything. -/
def failing (ms : Nat) : Async Body.Stream := do
  let s ← Body.mkStream
  background do
    sleep (.ofNat ms)
    try s.closeWithError (.userError "boom") catch _ => pure ()
  return s

/-- A response body of unknown length that sends `chunks` after `ms`, then ends. -/
def producing (ms : Nat) (chunks : List String) : Async Body.Stream := do
  let s ← Body.mkStream
  background do
    sleep (.ofNat ms)
    for c in chunks do s.send (Chunk.ofByteArray c.toUTF8)
    s.close
  return s

/-- Reads from `client` until the server closes the connection. -/
def readAll (client : Mock.Client) : Async ByteArray := do
  let mut out := ByteArray.empty
  repeat
    match ← client.recv? with
    | none => break
    | some chunk => out := out ++ chunk
  return out

/-- Serves `raw`, answered with `body`; returns what the client read and the reports. -/
def serve (raw : String) (body : Async Body.Stream := failing 30) : IO (String × Array String) :=
  Async.block do
    let failures ← IO.mkRef (#[] : Array String)
    let handler : Server.StatelessHandler := {
      onRequest := fun _ => do return Response.ok.body (Body.Any.ofBody (← body))
      onFailure := fun e => failures.modify (·.push (toString e)) }
    let (client, server) ← Mock.new
    client.send raw.toUTF8
    let serving ← async (Server.serveConnection server handler defaultConfig).run
    let out ← readAll client
    await serving
    return (String.fromUTF8! out, ← failures.get)

/-- A 500 that closes the connection, with no trace of the handler's response. -/
def isServerError (out : String) : Bool :=
  out.startsWith "HTTP/1.1 500 Internal Server Error\r\n" &&
    (out.splitOn "Connection: close\r\n").length == 2 && (out.splitOn "200 OK").length == 1

#eval show IO Unit from do
  let cases := [
    ("keep-alive", "GET / HTTP/1.1\r\nHost: x\r\n\r\n"),
    ("HTTP/1.0", "GET / HTTP/1.0\r\nHost: x\r\n\r\n"),
    ("Connection: close", "GET / HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n")]
  let mut failed := #[]
  for (name, raw) in cases do
    let (out, reports) ← serve raw
    unless isServerError out && reports == #["boom"] do
      failed := failed.push s!"{name}: got {out.quote} with reports {reports}"
  let ok := [
    ("HTTP/1.0, two chunks", "GET / HTTP/1.0\r\nHost: x\r\n\r\n", ["ab", "cd"],
      "HTTP/1.1 200 OK\r\nServer: LeanHTTP/1.1\r\nConnection: close\r\n\r\nabcd"),
    ("HTTP/1.0, empty", "GET / HTTP/1.0\r\nHost: x\r\n\r\n", [],
      "HTTP/1.1 200 OK\r\nServer: LeanHTTP/1.1\r\nConnection: close\r\nContent-Length: 0\r\n\r\n"),
    ("Connection: close, one chunk", "GET / HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n", ["abcd"],
      "HTTP/1.1 200 OK\r\nServer: LeanHTTP/1.1\r\nConnection: close\r\nTransfer-Encoding: chunked\r\n\r\n4\r\nabcd\r\n0\r\n\r\n")]
  for (name, raw, chunks, want) in ok do
    let (out, reports) ← serve raw (producing 30 chunks)
    unless out == want && reports.isEmpty do
      failed := failed.push s!"{name}: got {out.quote} with reports {reports}"
  unless failed.isEmpty do
    throw <| IO.userError ("\n".intercalate failed.toList)
