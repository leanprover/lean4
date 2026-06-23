/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Http.Server
public import Std.Async
public import Std.Async.Timer
import Init.Data.String.Legacy

public section

open Std.Async
open Std Http

namespace Std.Http.Internal.Test

abbrev TestHandler := Request Body.Stream → ContextAsync (Response Body.Any)

instance : Std.Http.Server.Handler TestHandler where
  onRequest handler request := handler request

/--
Default config for server tests. Short lingering timeout, no Date header.
-/
def defaultConfig : Config :=
  { lingeringTimeout := 1000, generateDate := false }

private def sendRaw
    (client : Mock.Client) (server : Mock.Server) (raw : ByteArray)
    (handler : TestHandler) (config : Config) : IO ByteArray :=
  Async.block do
    client.send raw
    Std.Http.Server.serveConnection server handler config |>.run
    let res ← client.recv?
    pure (res.getD .empty)

private def sendClose
    (client : Mock.Client) (server : Mock.Server) (raw : ByteArray)
    (handler : TestHandler) (config : Config) : IO ByteArray :=
  Async.block do
    client.send raw
    client.getSendChan.close
    Std.Http.Server.serveConnection server handler config |>.run
    let res ← client.recv?
    pure (res.getD .empty)

-- Timeout wrapper

private def withTimeout {α : Type} (name : String) (ms : Nat) (action : IO α) : IO α := do
  let task ← IO.asTask action
  let ticks := (ms + 9) / 10
  let rec loop : Nat → IO α
    | 0 => do IO.cancel task; throw <| IO.userError s!"'{name}' timed out after {ms}ms"
    | n + 1 => do
      if (← IO.getTaskState task) == .finished then
        match ← IO.wait task with
        | .ok x => pure x
        | .error e => throw e
      else IO.sleep 10; loop n
  loop ticks

-- Test grouping

/--
Run `tests` and wrap any failure message with the group name.
Use as `#eval runGroup "Topic" do ...`.
-/
def runGroup (name : String) (tests : IO Unit) : IO Unit :=
  try tests
  catch e => throw (IO.userError s!"[{name}]\n{e}")

-- Per-test runners

/--
Create a fresh mock connection, send `raw`, and run assertions.
-/
def check
    (name : String)
    (raw : String)
    (handler : TestHandler)
    (expect : ByteArray → IO Unit)
    (config : Config := defaultConfig) : IO Unit := do
  let (client, server) ← Mock.new
  let response ← sendRaw client server raw.toUTF8 handler config
  try expect response
  catch e => throw (IO.userError s!"[{name}] {e}")

/--
Like `check` but closes the client channel before running the server.
Use for tests involving truncated input or silent-close (EOF-triggered behavior).
-/
def checkClose
    (name : String)
    (raw : String)
    (handler : TestHandler)
    (expect : ByteArray → IO Unit)
    (config : Config := defaultConfig) : IO Unit := do
  let (client, server) ← Mock.new
  let response ← sendClose client server raw.toUTF8 handler config
  try expect response
  catch e => throw (IO.userError s!"[{name}] {e}")

/--
Like `check` wrapped in a wall-clock timeout.
Required when the test involves streaming, async timers, or keep-alive behavior.
-/
def checkTimed
    (name : String)
    (ms : Nat := 2000)
    (raw : String)
    (handler : TestHandler)
    (expect : ByteArray → IO Unit)
    (config : Config := defaultConfig) : IO Unit :=
  withTimeout name ms <| check name raw handler expect config

-- Assertion helpers

/--
Assert the response starts with `prefix_` (e.g. `"HTTP/1.1 200"`).
-/
def assertStatus (response : ByteArray) (prefix_ : String) : IO Unit := do
  let text := String.fromUTF8! response
  unless text.startsWith prefix_ do
    throw <| IO.userError s!"expected status {prefix_.quote}, got:\n{text.quote}"

/--
Assert the response is byte-for-byte equal to `expected`.
Use sparingly — prefer `assertStatus` + `assertContains` for 200 responses.
-/
def assertExact (response : ByteArray) (expected : String) : IO Unit := do
  let text := String.fromUTF8! response
  unless text == expected do
    throw <| IO.userError s!"expected:\n{expected.quote}\ngot:\n{text.quote}"

/--
Assert `needle` appears anywhere in the response.
-/
def assertContains (response : ByteArray) (needle : String) : IO Unit := do
  let text := String.fromUTF8! response
  unless text.contains needle do
    throw <| IO.userError s!"expected to contain {needle.quote}, got:\n{text.quote}"

/--
Assert `needle` does NOT appear in the response.
-/
def assertAbsent (response : ByteArray) (needle : String) : IO Unit := do
  let text := String.fromUTF8! response
  if text.contains needle then
    throw <| IO.userError s!"expected NOT to contain {needle.quote}, got:\n{text.quote}"

/--
Assert the response contains exactly `n` occurrences of `"HTTP/1.1 "`.
-/
def assertResponseCount (response : ByteArray) (n : Nat) : IO Unit := do
  let text := String.fromUTF8! response
  let got := (text.splitOn "HTTP/1.1 ").length - 1
  unless got == n do
    throw <| IO.userError s!"expected {n} HTTP/1.1 responses, got {got}:\n{text.quote}"

-- Common fixed response strings

def r400 : String :=
  "HTTP/1.1 400 Bad Request\x0d\nServer: LeanHTTP/1.1\x0d\nConnection: close\x0d\nContent-Length: 0\x0d\n\x0d\n"

def r408 : String :=
  "HTTP/1.1 408 Request Timeout\x0d\nServer: LeanHTTP/1.1\x0d\nConnection: close\x0d\nContent-Length: 0\x0d\n\x0d\n"

def r413 : String :=
  "HTTP/1.1 413 Content Too Large\x0d\nServer: LeanHTTP/1.1\x0d\nConnection: close\x0d\nContent-Length: 0\x0d\n\x0d\n"

def r417 : String :=
  "HTTP/1.1 417 Expectation Failed\x0d\nServer: LeanHTTP/1.1\x0d\nConnection: close\x0d\nContent-Length: 0\x0d\n\x0d\n"

def r431 : String :=
  "HTTP/1.1 431 Request Header Fields Too Large\x0d\nServer: LeanHTTP/1.1\x0d\nConnection: close\x0d\nContent-Length: 0\x0d\n\x0d\n"

def r505 : String :=
  "HTTP/1.1 505 HTTP Version Not Supported\x0d\nServer: LeanHTTP/1.1\x0d\nConnection: close\x0d\nContent-Length: 0\x0d\n\x0d\n"

-- Standard handlers

/--
Always respond 200 "ok" without reading the request body.
-/
def okHandler : TestHandler := fun _ => Response.ok |>.text "ok"

/--
Read the full request body and echo it back as text/plain.
-/
def echoHandler : TestHandler := fun req => do
  Response.ok |>.text (← req.body.readAll)

/--
Respond 200 with the request URI as the body.
-/
def uriHandler : TestHandler := fun req =>
  Response.ok |>.text (toString req.line.uri)

-- Request builder helpers

/--
Minimal GET request. `extra` is appended as raw header lines (each ending with `\x0d\n`)
before the blank line.
-/
def mkGet (path : String := "/") (extra : String := "") : String :=
  s!"GET {path} HTTP/1.1\x0d\nHost: example.com\x0d\n{extra}\x0d\n"

/--
GET with `Connection: close`.
-/
def mkGetClose (path : String := "/") : String :=
  mkGet path "Connection: close\x0d\n"

/--
POST with a fixed Content-Length body. `extra` is appended before the blank line.
-/
def mkPost (path : String) (body : String) (extra : String := "") : String :=
  s!"POST {path} HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: {body.toUTF8.size}\x0d\n{extra}\x0d\n{body}"

/--
POST with Transfer-Encoding: chunked. `chunkedBody` is the pre-formatted body
(use `chunk` + `chunkEnd` to build it).
-/
def mkChunked (path : String) (chunkedBody : String) (extra : String := "") : String :=
  s!"POST {path} HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\n{extra}\x0d\n{chunkedBody}"

/--
Format a single chunk: `<hex-size>\x0d\n<data>\x0d\n`.
-/
def chunk (data : String) : String :=
  let hexSize := Nat.toDigits 16 data.toUTF8.size |> String.ofList
  s!"{hexSize}\x0d\n{data}\x0d\n"

/--
The terminal zero-chunk that ends a chunked body.
-/
def chunkEnd : String := "0\x0d\n\x0d\n"

end Std.Http.Internal.Test
