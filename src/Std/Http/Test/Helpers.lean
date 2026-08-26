/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Http.Server
public import Std.Http.Client
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

-- HTTP client helpers

namespace ClientHelpers

/-- Run a client test action with a wall-clock timeout. -/
def runWithTimeout (name : String) (timeoutMs : Nat := 3000) (action : IO Unit) : IO Unit := do
  let task ← IO.asTask action
  let ticks := (timeoutMs + 9) / 10
  let rec loop (remaining : Nat) : IO Unit := do
    if (← IO.getTaskState task) == .finished then
      match (← IO.wait task) with
      | .ok x => pure x
      | .error err => throw err
    else
      match remaining with
      | 0 =>
        IO.cancel task
        throw <| IO.userError s!"Test '{name}' timed out after {timeoutMs}ms"
      | n + 1 =>
        IO.sleep 10
        loop n
  loop ticks

/-- A domain-name host, for tests that name their peers as literals. -/
def hostName! (host : String) : URI.Host :=
  match URI.DomainName.ofString? host with
  | some name => .name name
  | none => panic! s!"invalid host name: {host.quote}"

/-- The origin a mock client connection is opened for. -/
def origin (host : String := "example.com") (port : UInt16 := 80) (scheme : String := "http") :
    URI.Origin :=
  { scheme := URI.Scheme.ofString! scheme, host := hostName! host, port }

/-- Build a raw HTTP/1.1 response. -/
def rawResp
    (status : String) (hdrs : Array (String × String)) (body : String) : ByteArray :=
  let hdrLines := hdrs.foldl (fun s (k, v) => s ++ s!"{k}: {v}\r\n") ""
  s!"HTTP/1.1 {status}\r\n{hdrLines}\r\n{body}".toUTF8

/-- Parse `Content-Length` from a raw HTTP header block. Returns 0 when absent. -/
private def parseContentLength (headerText : String) : Nat := Id.run do
  let lines := headerText.splitOn "\r\n"
  for line in lines do
    let lower := line.toLower
    if lower.startsWith "content-length:" then
      let rest := line.drop "content-length:".length
      return rest.trimAscii.toNat?.getD 0
  return 0

/--
Drain the mock until a complete request has been consumed, including a fixed-length or chunked body.
-/
def drainRequest (mockClient : Mock.Client) : Async ByteArray := do
  let mut bytes := ByteArray.empty
  let mut headerEnd : Nat := 0
  repeat
    if (String.fromUTF8! bytes).contains "\r\n\r\n" then
      let mut i := 0
      while i + 4 ≤ bytes.size do
        if bytes[i]! == 13 && bytes[i+1]! == 10 && bytes[i+2]! == 13 && bytes[i+3]! == 10 then
          headerEnd := i + 4
          break
        i := i + 1
      break
    let some chunk ← mockClient.recv?
      | throw (IO.userError "connection closed before headers")
    bytes := bytes ++ chunk
  let headerText := String.fromUTF8! (bytes.extract 0 headerEnd)
  if headerText.toLower.contains "transfer-encoding:" then
    while !(String.fromUTF8! bytes).endsWith "0\r\n\r\n" do
      let some chunk ← mockClient.recv?
        | throw (IO.userError "connection closed mid-chunked")
      bytes := bytes ++ chunk
  else
    let cl := parseContentLength headerText
    while bytes.size < headerEnd + cl do
      let some chunk ← mockClient.recv?
        | throw (IO.userError "connection closed before full CL body")
      bytes := bytes ++ chunk
  pure bytes

/--
A `Client` wired to mock transports, together with the origin its requests target and the
connections its connector has handed out. Bundling these keeps test bodies free of the `origin`
argument `Client.send` takes and lets a test reach the transport under test.
-/
structure TestClient where
  /-- The client under test. -/
  client : Client

  /-- Origin every `TestClient.send` targets. -/
  origin : URI.Origin

  /-- Connections opened by the client's connector, in the order they were opened. -/
  opened : IO.Ref (Array Client.Connection)

namespace TestClient

/-- Send a request to the client's origin. -/
def send {β : Type} [Coe β Body.Any] (self : TestClient) (request : Request β)
    (overrides : Client.RequestOverrides := {}) : Async (Response Body.Stream) :=
  self.client.send self.origin request overrides

/-- The connection the client most recently opened. -/
def connection (self : TestClient) : Async Client.Connection := do
  let some connection := (← self.opened.get).back?
    | throw (IO.userError "the client has not opened a connection yet")
  pure connection

end TestClient

/--
Create an HTTP client whose connector always dials `mockServer`. Retries are disabled so that a
transport failure surfaces to the test instead of being replayed on a second connection.
-/
def mkClient (mockServer : Mock.Server) (config : Client.Config := {})
    (port : UInt16 := 80) (scheme : String := "http") : Async TestClient := do
  let some domain := URI.DomainName.ofString? "example.com"
    | throw (IO.userError "DomainName parse failed")
  let opened ← IO.mkRef (#[] : Array Client.Connection)
  let connect : Client.Connector := fun _ _ _ config => do
    let connection ← Client.Connection.new mockServer config
    opened.modify (·.push connection)
    return .ok connection
  let client ← Client.new config connect (maxRetries := 0)
  pure {
    client
    origin := { scheme := URI.Scheme.ofString! scheme, host := .name domain, port }
    opened
  }

/--
Create a client whose connector hands out `servers` in order, one per connection it opens. The
returned ref records the origin of every connection *after* the first, so a test can assert where a
hop was dialled as well as what was written on it. Opening more connections than there are servers
fails the test.
-/
def mkFollowingClient (servers : Array Mock.Server) (config : Client.Config := {})
    (port : UInt16 := 80) (scheme : String := "http") :
    Async (TestClient × IO.Ref (Array URI.Origin)) := do
  if servers.isEmpty then
    throw (IO.userError "mkFollowingClient needs at least one server")
  let some domain := URI.DomainName.ofString? "example.com"
    | throw (IO.userError "DomainName parse failed")
  let nextServer ← IO.mkRef 0
  let dialled ← IO.mkRef (#[] : Array URI.Origin)
  let opened ← IO.mkRef (#[] : Array Client.Connection)

  let connect : Client.Connector := fun scheme host port config => do
    let index ← nextServer.modifyGet fun index => (index, index + 1)
    let some server := servers[index]?
      | throw <| IO.userError
          s!"the client opened more than {servers.size} connections (connection {index + 1} wanted {host})"
    if index > 0 then
      dialled.modify (·.push { scheme, host, port })
    let connection ← Client.Connection.new server config
    opened.modify (·.push connection)
    return .ok connection

  let client ← Client.new config connect (maxRetries := 0)
  let testClient : TestClient := {
    client
    origin := { scheme := URI.Scheme.ofString! scheme, host := .name domain, port }
    opened
  }
  pure (testClient, dialled)

/--
Create a client that dials `mockServer` for its first connection and refuses every later one,
recording the origin it was asked for. A redirect-scheme guard is about a dial that must *never*
happen, so witnessing its absence needs a connector that could have dialled.
-/
def mkRefusingClient (mockServer : Mock.Server) (config : Client.Config := {}) :
    Async (TestClient × IO.Ref (Option URI.Origin)) := do
  let some domain := URI.DomainName.ofString? "example.com"
    | throw (IO.userError "DomainName parse failed")
  let dialled ← IO.mkRef (none : Option URI.Origin)
  let opened ← IO.mkRef (#[] : Array Client.Connection)
  let firstDial ← IO.mkRef true

  let connect : Client.Connector := fun scheme host port config => do
    if ← firstDial.modifyGet (fun first => (first, false)) then
      let connection ← Client.Connection.new mockServer config
      opened.modify (·.push connection)
      return .ok connection
    dialled.set (some { scheme, host, port })
    return .error (.connect "the redirect target must never be dialled")

  let client ← Client.new config connect (maxRetries := 0)
  let testClient : TestClient := {
    client
    origin := { scheme := URI.Scheme.ofString! "http", host := .name domain, port := 80 }
    opened
  }
  pure (testClient, dialled)

/-- Send a client request in the background and expose its result through a promise. -/
def sendInBackground {β : Type} [Coe β Body.Any]
    (client : TestClient) (request : Request β)
    (overrides : Client.RequestOverrides := {}) :
    Async (IO.Promise (Except String (Response Body.Stream))) := do
  let resultPromise : IO.Promise (Except String (Response Body.Stream)) ← IO.Promise.new
  background do
    let result ← try
        let resp ← client.send request overrides
        pure (Except.ok resp)
      catch e => pure (Except.error (toString e))
    discard <| resultPromise.resolve result
  pure resultPromise

end ClientHelpers

end Std.Http.Internal.Test
