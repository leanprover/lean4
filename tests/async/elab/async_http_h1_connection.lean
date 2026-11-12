module

import Std.Http.Test.Helpers
import Std.Http.Test.Machine

/-!
# HTTP/1.1 connections

Whether a connection persists, how `Connection` options are read and written, pipelining, where the
next request starts after a body, errors that end a connection, and the request count. Machine tables
first, then `serveConnection` tables. RFC 9112 §9.3, §9.6; RFC 9110 §7.6.1, §7.8. Regressions:
#12151.
-/

open Std Http
open Std.Async
open Std.Http.Internal
open Std.Http.Protocol.H1
open Std.Http.Internal.Test

private def mkGet10 (path : String := "/") : String :=
  s!"GET {path} HTTP/1.0\r\n\r\n"

private def mkPostHead (path : String) (bodyLen : Nat) (extra : String := "") : String :=
  rawRequest "POST" path (extra := s!"Content-Length: {bodyLen}\r\n{extra}")

private def upgrade (connection : String) : Response.Head :=
  { status := .upgradeRequired,
    headers := Headers.empty |>.insert! "Upgrade" "TLS/1.2" |>.insert! "Connection" connection }

private def minimalGetRequest : Request.Head :=
  { method := .get, version := .v11, uri := RequestTarget.originForm! "/",
    headers := Headers.empty.insert! "Host" "example.com" }

/-- Steps `machine` `n` times and returns it with the bytes it wrote. -/
private def run (machine : Machine dir) (n : Nat := 4) : Machine dir × String := Id.run do
  let mut machine := machine
  let mut out := ByteArray.empty
  for _ in [0:n] do
    let (next, step) := machine.step
    machine := next
    out := out ++ step.output.toByteArray
  return (machine, String.fromUTF8! out)

private def expect (cond : Bool) (msg : String) : IO Unit :=
  unless cond do throw (IO.userError msg)

private def runPipelined
    (raw : String)
    (readBody : Bool := true)
    (config : Std.Http.Config := defaultConfig) : IO (ByteArray × Array String) := Async.block do
  let (client, server) ← Mock.new
  let seenRef ← IO.mkRef (#[] : Array String)

  let handler : TestHandler := fun req => do
    seenRef.modify (·.push (toString req.line.uri))
    let body ←
      if readBody then req.body.readAll
      else pure "<ignored>"
    Response.ok |>.text s!"{toString req.line.uri}:{body}"

  client.send raw.toUTF8
  client.getSendChan.close
  Std.Http.Server.serveConnection server handler config |>.run

  let response ← client.recv?
  let seen ← seenRef.get
  pure (response.getD .empty, seen)

private def assertSeenCount (seen : Array String) (expected : Nat) : IO Unit := do
  unless seen.size == expected do
    throw <| IO.userError s!"expected {expected} handler calls, got {seen.size}: {seen}"

private def runWithTimeout {α : Type} (name : String) (timeoutMs : Nat := 2000) (action : IO α) : IO α := do
  let task ← IO.asTask action
  let ticks := (timeoutMs + 9) / 10

  let rec loop (remaining : Nat) : IO α := do
    if (← IO.getTaskState task) == .finished then
      match (← IO.wait task) with
      | .ok x => pure x
      | .error err => throw err
    else
      match remaining with
      | 0 =>
        IO.cancel task
        throw <| IO.userError s!"Test '{name}' timed out after {timeoutMs}ms (possible hang/loop)"
      | n + 1 =>
        IO.sleep 10
        loop n

  loop ticks

private def sendRaw (client : Mock.Client) (server : Mock.Server) (raw : ByteArray)
    (handler : TestHandler) (config : Std.Http.Config := { lingeringTimeout := 500, generateDate := false }) : IO ByteArray := Async.block do
  client.send raw
  Std.Http.Server.serveConnection server handler config
    |>.run
  let res ← client.recv?
  pure <| res.getD .empty

private def sendRawTimed (name : String) (raw : ByteArray)
    (handler : TestHandler) (config : Std.Http.Config := { lingeringTimeout := 500, generateDate := false }) : IO ByteArray :=
  runWithTimeout name 2000 do
    let (client, server) ← Mock.new
    sendRaw client server raw handler config

private def runClosedClientTimed (name : String) (raw : ByteArray)
    (handler : TestHandler) (config : Std.Http.Config := { lingeringTimeout := 500, generateDate := false }) : IO Unit :=
  runWithTimeout name 2000 do
    Async.block do
      let (client, server) ← Mock.new
      client.send raw
      client.close
      Std.Http.Server.serveConnection server handler config
        |>.run

private def countOccurrences (s : String) (needle : String) : Nat :=
  if needle.isEmpty then 0 else (s.splitOn needle).length - 1

private def assertStatusPrefix (name : String) (response : ByteArray) (prefix_ : String) : IO Unit := do
  let text := String.fromUTF8! response
  unless text.startsWith prefix_ do
    throw <| IO.userError s!"Test '{name}' failed:\nExpected prefix: {prefix_.quote}\nGot:\n{text.quote}"

private def assertNotContains (name : String) (response : ByteArray) (needle : String) : IO Unit := do
  let text := String.fromUTF8! response
  if text.contains needle then
    throw <| IO.userError s!"Test '{name}' failed:\nDid not expect {needle.quote}\nGot:\n{text.quote}"

private def assertEndsWith (name : String) (response : ByteArray) (suffix_ : String) : IO Unit := do
  let text := String.fromUTF8! response
  unless text.endsWith suffix_ do
    throw <| IO.userError s!"Test '{name}' failed:\nExpected suffix: {suffix_.quote}\nGot:\n{text.quote}"

private def assertStatusCount (name : String) (response : ByteArray) (expected : Nat) : IO Unit := do
  let text := String.fromUTF8! response
  let got := countOccurrences text "HTTP/1.1 "
  unless got == expected do
    throw <| IO.userError s!"Test '{name}' failed:\nExpected {expected} HTTP responses, got {got}\n{text.quote}"

private def onesChunked (n : Nat) : String := Id.run do
  let mut body := ""
  for i in [0:n] do
    body := body ++ s!"{toString i |>.length}\x0d\n{toString i}\x0d\n"
  body ++ "0\x0d\n\x0d\n"

private def closeChannelIdempotent {α : Type} (ch : Std.CloseableChannel α) : IO Unit := do
  match ← EIO.toBaseIO ch.close with
  | .ok _ => pure ()
  | .error .alreadyClosed => pure ()
  | .error err => throw <| IO.userError (toString err)

private def responseText (response : ByteArray) : String :=
  String.fromUTF8! response

private def nextSeed (seed : Nat) : Nat :=
  (1664525 * seed + 1013904223) % 4294967296

private def randBelow (seed : Nat) (maxExclusive : Nat) : Nat × Nat :=
  let seed' := nextSeed seed
  if maxExclusive == 0 then
    (0, seed')
  else
    (seed' % maxExclusive, seed')

private def randIn (seed : Nat) (low : Nat) (high : Nat) : Nat × Nat :=
  if high < low then
    (low, seed)
  else
    let (n, seed') := randBelow seed (high - low + 1)
    (low + n, seed')

private def randomAsciiBytes (seed : Nat) (len : Nat) : ByteArray × Nat := Id.run do
  let mut s := seed
  let mut out := ByteArray.empty

  for _ in [0:len] do
    let (r, s') := randBelow s 38
    s := s'

    let code :=
      if r < 26 then
        97 + r
      else if r < 36 then
        48 + (r - 26)
      else if r == 36 then
        45
      else
        95

    out := out.push (UInt8.ofNat code)

  (out, s)

private def runPipelinedReadAll
    (raw : ByteArray)
    (config : Std.Http.Config := defaultConfig) : IO (ByteArray × Array String) := Async.block do
  let (client, server) ← Mock.new
  let seenRef ← IO.mkRef (#[] : Array String)

  let handler : TestHandler := fun req => do
    let uri := toString req.line.uri
    seenRef.modify (·.push uri)
    let _body : String ← req.body.readAll
    Response.ok |>.text uri

  client.send raw
  closeChannelIdempotent client.getSendChan

  Std.Http.Server.serveConnection server handler config
    |>.run

  let response ← client.recv?
  let seen ← seenRef.get
  pure (response.getD .empty, seen)

private def fuzzCompleteFirstBodyAllowsPipeline (iterations : Nat) (seed0 : Nat) : IO Unit := do
  let mut seed := seed0

  for i in [0:iterations] do
    let caseSeed := seed

    let (len, seed1) := randIn seed 0 32
    seed := seed1

    let (body, seed2) := randomAsciiBytes seed len
    seed := seed2

    let uri1 := s!"/first-complete-{i}"
    let req1 :=
      s!"POST {uri1} HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: {len}\x0d\n\x0d\n".toUTF8 ++ body
    let req2 := "GET /second HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8

    let (response, seen) ← runPipelinedReadAll (req1 ++ req2)

    let text := responseText response
    assertStatusCount s!"fuzzCompleteFirstBodyAllowsPipeline case={i} seed={caseSeed}" response 2

    unless text.contains uri1 do
      throw <| IO.userError s!"fuzzCompleteFirstBodyAllowsPipeline case={i} seed={caseSeed} failed:\nMissing first URI {uri1.quote}\n{text.quote}"

    unless text.contains "/second" do
      throw <| IO.userError s!"fuzzCompleteFirstBodyAllowsPipeline case={i} seed={caseSeed} failed:\nMissing second response\n{text.quote}"

    if seen.size != 2 ∨ seen[0]! != uri1 ∨ seen[1]! != "/second" then
      throw <| IO.userError s!"fuzzCompleteFirstBodyAllowsPipeline case={i} seed={caseSeed} failed:\nExpected seen=[{uri1.quote}, \"/second\"] got {seen}"

private def sendRawAndClose
    (client : Mock.Client) (server : Mock.Server) (raw : ByteArray)
    (handler : TestHandler) (config : Std.Http.Config) : IO ByteArray := Async.block do
  client.send raw
  closeChannelIdempotent client.getSendChan
  Std.Http.Server.serveConnection server handler config |>.run
  let res ← client.recv?
  pure (res.getD .empty)

private def fuzzMaxMessagesPerConnection (iterations : Nat) (seed0 : Nat) : IO Unit := do
  let limit : Nat := 3
  let config : Std.Http.Config := {
    lingeringTimeout := 1000
    generateDate := false
    maxRequests := limit
  }
  let mut seed := seed0
  for i in [0:iterations] do
    let caseSeed := seed
    let (reqCount, s1) := randIn seed 1 (limit + 3); seed := s1

    -- Build reqCount keep-alive requests followed by close
    let mut raw := ByteArray.empty
    for j in [0:reqCount] do
      let connHeader :=
        if j + 1 == reqCount then "Connection: close\x0d\n" else "Connection: keep-alive\x0d\n"
      raw := raw ++ s!"GET /msg-{i}-{j} HTTP/1.1\x0d\nHost: example.com\x0d\n{connHeader}\x0d\n".toUTF8

    let (client, server) ← Mock.new
    let response ← sendRawAndClose client server raw okHandler config
    let text := String.fromUTF8! response
    let seen := countOccurrences text "HTTP/1.1 200"
    let expected := Nat.min reqCount limit
    if seen != expected then
      throw <| IO.userError
        s!"fuzzMaxMessages iter={i} seed={caseSeed} reqCount={reqCount}: expected {expected} responses, got {seen}\n{text.quote}"
    -- The last response the server writes, whether the request asked or the limit was reached,
    -- announces that the connection closes.
    let last := ((text.splitOn "HTTP/1.1 200").getLast?).getD ""
    unless last.contains "Connection: close" do
      throw <| IO.userError
        s!"fuzzMaxMessages iter={i} seed={caseSeed} reqCount={reqCount}: the last response lacks Connection: close\n{text.quote}"

/-- Steps `machine` until it halts; `none` if it has not halted after 16 steps. -/
private def stepsToHalt (machine : Machine .receiving) : Option Nat := Id.run do
  let mut machine := machine
  for i in [0:16] do
    if machine.halted then return some i
    machine := machine.step.1
  return none

/-- A server machine that has read `input` and is streaming a response to its first request. -/
private def streaming (input : String) : Machine .receiving :=
  let machine := (({ config := {} } : Machine .receiving).feed input.toUTF8).step.1
  (machine.send { status := .ok } |>.sendData #[Chunk.ofByteArray "hello".toUTF8]).step.1

private def getRequest : String := "GET / HTTP/1.1\r\nHost: a\r\n\r\n"

/-- A serverAfter machine that has read `request`. -/
private def serverAfter (request : String) : Machine .receiving :=
  (({ config := {} } : Machine .receiving).feed request.toUTF8).step.1

private def headers (fields : List (Header.Name × String)) : Headers :=
  fields.foldl (fun hs (name, value) => hs.insert name (Header.Value.ofString! value)) .empty

private def abc : Array Chunk := #[Chunk.ofByteArray "abc".toUTF8]

/-! ## Persistence defaults (RFC 9112 §9.3) -/

#eval checkCases "Persistence defaults: machine" #[
    ("§9.3: HTTP/1.1 default keep-alive = true", do
      -- §9.3: HTTP/1.1 connections are persistent by default
      MachineTester.receiving "§9.3: HTTP/1.1 default keep-alive = true"
        |>.feed (mkGet "/") |>.step |>.assertNoError |>.assertKeepAlive |>.run),
    ("§9.3: HTTP/1.0 default keep-alive = false", do
      -- §9.3: HTTP/1.0 connections are not persistent by default
      MachineTester.receiving "§9.3: HTTP/1.0 default keep-alive = false"
        |>.feed (mkGet10 "/") |>.step |>.assertNoError |>.assertNotKeepAlive |>.run),
    ("§9.3: HTTP/1.1 explicit Connection:keep-alive → keepAlive = true", do
      -- §9.3: explicit (redundant) Connection: keep-alive MUST NOT suppress default keep-alive
      MachineTester.receiving "§9.3: HTTP/1.1 explicit Connection:keep-alive → keepAlive = true"
        |>.feed "GET / HTTP/1.1\r\nHost: example.com\r\nConnection: keep-alive\r\n\r\n"
        |>.step |>.assertNoError |>.assertKeepAlive |>.run),
    ("RFC 9112 §9.3: client receives HTTP/1.0 response → keepAlive = false", do
      -- RFC 2616 §8.1: HTTP/1.0 does not default to persistent connections
      MachineTester.sending "RFC 9112 §9.3: client receives HTTP/1.0 response → keepAlive = false"
        |>.send minimalGetRequest |>.step
        |>.feed "HTTP/1.0 200 OK\r\nContent-Length: 0\r\n\r\n"
        |>.step |>.assertNoError |>.assertNotKeepAlive |>.run),
    ("RFC 9112 §9.3: HTTP/1.0 Connection:keep-alive → keep-alive = true", do
      -- RFC 2616 §19.7.1: HTTP/1.0 + Connection: keep-alive → keep-alive enabled
      MachineTester.receiving "RFC 9112 §9.3: HTTP/1.0 Connection:keep-alive → keep-alive = true"
        |>.feed "GET / HTTP/1.0\r\nConnection: keep-alive\r\n\r\n"
        |>.step |>.assertNoError |>.assertKeepAlive |>.run),
    ("RFC 9112 §9.3: client receives HTTP/1.0 + Connection:keep-alive → keepAlive = true", do
      -- §19.7.1: client side — response Connection:keep-alive → keepAlive = true
      MachineTester.sending "RFC 9112 §9.3: client receives HTTP/1.0 + Connection:keep-alive → keepAlive = true"
        |>.send minimalGetRequest |>.step
        |>.feed "HTTP/1.0 200 OK\r\nConnection: keep-alive\r\nContent-Length: 0\r\n\r\n"
        |>.step |>.assertNoError |>.assertKeepAlive |>.run),
    ("§6.2: HTTP/1.0 keep-alive request → HTTP/1.1 status line, keep-alive echoed", do
      MachineTester.receiving "§6.2: HTTP/1.0 keep-alive request → HTTP/1.1 status line, keep-alive echoed"
        |>.feed "GET / HTTP/1.0\r\nConnection: keep-alive\r\n\r\n" |>.step
        |>.send { status := .ok } |>.setKnownSize (.fixed 0) |>.userClosedBody
        |>.step |>.step
        |>.assertOutputStartsWith "HTTP/1.1 200 OK\r\n" "expected an HTTP/1.1 status line"
        |>.assertOutputContains "Connection: keep-alive\r\n" "expected the HTTP/1.0 keep-alive echo"
        |>.assertKeepAlive |>.run)
  ] (·.2)


-- RFC 9112 §9.3: a bodyless status does not end a persistent connection.
#eval checkCases "204 and 304 keep the connection" #[
    ("204, HTTP/1.0 keep-alive", Status.noContent, "GET /1 HTTP/1.0\x0d\nConnection: keep-alive\x0d\n\x0d\nGET /2 HTTP/1.0\x0d\n\x0d\n"),
    ("304, HTTP/1.0 keep-alive", .notModified, "GET /1 HTTP/1.0\x0d\nConnection: keep-alive\x0d\n\x0d\nGET /2 HTTP/1.0\x0d\n\x0d\n"),
    ("204, HTTP/1.1", .noContent, "GET /1 HTTP/1.1\x0d\nHost: a\x0d\n\x0d\nGET /2 HTTP/1.1\x0d\nHost: a\x0d\nConnection: close\x0d\n\x0d\n"),
    ("304, HTTP/1.1", .notModified, "GET /1 HTTP/1.1\x0d\nHost: a\x0d\n\x0d\nGET /2 HTTP/1.1\x0d\nHost: a\x0d\nConnection: close\x0d\n\x0d\n")
  ] fun (_, status, raw) => checkHandler raw (show TestHandler from fun _ => Response.withStatus status |>.text "") (.responses 2)

/-! ## Connection: close (RFC 9112 §9.6) -/

#eval checkCases "Connection: close: machine" #[
    ("§9.6: HTTP/1.1 Connection:close → keep-alive = false", do
      -- §9.6: Connection: close in request → keep-alive = false
      MachineTester.receiving "§9.6: HTTP/1.1 Connection:close → keep-alive = false"
        |>.feed "GET / HTTP/1.1\r\nHost: example.com\r\nConnection: close\r\n\r\n"
        |>.step |>.assertNoError |>.assertNotKeepAlive |>.run),
    ("§9.6: Connection:close injected into response when not keep-alive", do
      -- §9.6: Connection: close injected into response when keep-alive is false
      MachineTester.receiving "§9.6: Connection:close injected into response when not keep-alive"
        |>.feed "GET / HTTP/1.1\r\nHost: example.com\r\nConnection: close\r\n\r\n"
        |>.step |>.assertNotKeepAlive
        |>.send { status := .ok } |>.setKnownSize (.fixed 0) |>.userClosedBody |>.step
        |>.assertOutputContains "Connection: close" "expected Connection: close in response" |>.run),
    ("§9.6: handler Connection:close on keep-alive request → connection closed", do
      -- §9.6: a `Connection: close` response header set by the handler ends a keep-alive connection
      MachineTester.receiving "§9.6: handler Connection:close on keep-alive request → connection closed"
        |>.feed (mkGet "/first" ++ mkGet "/second") |>.step |>.assertHasEndHeaders |>.assertKeepAlive
        |>.send { status := .ok, headers := Headers.empty.insert .connection (.mk "close") }
        |>.setKnownSize (.fixed 0) |>.userClosedBody |>.step
        |>.assertNotKeepAlive
        |>.assertOutputContains "Connection: close" "expected Connection: close in response"
        |>.assertHasEvent (fun | .close => true | _ => false) "expected .close after the response"
        |>.assertNoEvent (fun | .next => true | _ => false) "expected the pipelined request to be dropped"
        |>.step |>.assertHalted |>.run),
    ("§9.6: the error responses of `closeWithError` end a keep-alive connection", do
      -- §9.6: the error responses of `closeWithError` end a keep-alive connection
      for status in #[Status.internalServerError, .requestTimeout, .serviceUnavailable] do
        MachineTester.receiving s!"§9.6: closeWithError {status.toCode} on keep-alive request → connection closed"
          |>.feed (mkGet "/first" ++ mkGet "/second") |>.step |>.assertHasEndHeaders |>.assertKeepAlive
          |>.closeWithError status |>.step
          |>.assertNotKeepAlive
          |>.assertOutputStartsWith s!"HTTP/1.1 {status.toCode} " "expected the error status line"
          |>.assertOutputContains "Connection: close" "expected Connection: close in the error response"
          |>.assertHasEvent (fun | .close => true | _ => false) "expected .close after the error response"
          |>.assertNoEvent (fun | .next => true | _ => false) "expected the pipelined request to be dropped"
          |>.run),
    ("§9.6: HTTP/1.1 response Connection:close → keep-alive = false", do
      -- §9.6: HTTP/1.1 response with Connection: close → keep-alive disabled
      MachineTester.sending "§9.6: HTTP/1.1 response Connection:close → keep-alive = false"
        |>.send minimalGetRequest |>.step
        |>.feed "HTTP/1.1 200 OK\r\nConnection: close\r\nContent-Length: 0\r\n\r\n"
        |>.step |>.assertNoError |>.assertNotKeepAlive |>.run)
  ] (·.2)

#eval checkCases "Connection: close: async_http_connection_options.lean" #[
    ("HTTP/1.0 close wins",
      do
        for value in ["keep-alive, close", "close, keep-alive"] do
          check s!"Connection: {value}"
            s!"GET /1 HTTP/1.0\x0d\nConnection: {value}\x0d\n\x0d\nGET /2 HTTP/1.0\x0d\n\x0d\n"
            uriHandler fun r => do
              assertResponseCount r 1
              assertContains r "Connection: close"
              assertAbsent r "/2"),
    ("A client's HTTP/1.0 request that lists both `keep-alive` and `close` goes out with `close`, and",
      show IO Unit from do
      let headers := Headers.empty
        |>.insert Header.Name.host (.mk "a")
        |>.insert Header.Name.connection (.mk "keep-alive, close")
      let head : Request.Head := { method := .get, version := .v10, uri := RequestTarget.parse! "/", headers }
      let m : Machine .sending := { config := {} }
      let (m, out) := run (m.setKnownSize (.fixed 0) |>.send head |>.userClosedBody)
      expect (out.contains "Connection: close" && !out.contains "keep-alive")
        s!"client HTTP/1.0 request: expected Connection: close, got {out.quote}"
      expect (!m.keepAlive) "client HTTP/1.0 request with close: the machine kept the connection")
  ] (·.2)

#eval checkCases "Connection: close: async_http_keepalive.lean" #[
    ("Connection: close on first request blocks pipelined second",
      do
        check "Connection: close on first request blocks pipelined second"
          (raw :=
            "GET /first HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n" ++
            "GET /second HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")
          (handler := fun req => Response.ok |>.text (toString req.line.uri))
          (expect := fun r =>
            assertResponseCount r 1 *>
            assertContains r "/first" *>
            assertAbsent r "/second")),
    ("enableKeepAlive: false → one response only",
      do
        check "enableKeepAlive: false → one response only"
          (raw :=
            "GET /1 HTTP/1.1\x0d\nHost: example.com\x0d\n\x0d\n" ++
            "GET /2 HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")
          (handler := fun req => Response.ok |>.text (toString req.line.uri))
          (config := { defaultConfig with enableKeepAlive := false, lingeringTimeout := 3000 })
          (expect := fun r =>
            assertResponseCount r 1 *>
            assertContains r "/1" *>
            assertAbsent r "/2"))
  ] (·.2)


-- RFC 9110 §7.6.1: `Connection` is a case-insensitive list that may span lines and hold empty elements.
#eval checkCases "Connection lists: server" #[
    ("close, plus a second line with empty elements", "Connection: close\r\nconnectiON: fOo,, , BAR\r\n"),
    ("cLOse inside a list", "Connection: a, b, cLOse, foo\r\n")
  ] fun (label, fields) =>
    MachineTester.receiving label |>.feed s!"GET / HTTP/1.1\r\nHost: a\r\n{fields}\r\n" |>.step
      |>.assertNoError |>.assertNotKeepAlive |>.run

#eval checkCases "Connection lists: client" #[
    ("keep-alive, close on one line", "HTTP/1.1 200 OK\r\nConnection: keep-alive, close\r\nContent-Length: 0\r\n\r\n", false),
    ("keep-alive, then close on a second line", "HTTP/1.1 200 OK\r\nConnection: keep-alive\r\nConnection: close\r\nContent-Length: 0\r\n\r\n", false),
    ("HTTP/1.0", "HTTP/1.0 200 OK\r\nContent-Length: 0\r\n\r\n", false),
    ("HTTP/1.0 with keep-ALIVE", "HTTP/1.0 200 OK\r\nConnection: keep-ALIVE\r\nContent-Length: 0\r\n\r\n", true),
    ("HTTP/1.1", "HTTP/1.1 200 OK\r\nContent-Length: 0\r\n\r\n", true),
    ("HTTP/1.1 with cloSE", "HTTP/1.1 200 OK\r\nConnection: cloSE\r\nContent-Length: 0\r\n\r\n", false)
  ] fun (label, raw, reuse) =>
    let t := MachineTester.sending label |>.send minimalGetRequest |>.step |>.feed raw |>.step |>.assertNoError
    (if reuse then t.assertKeepAlive else t.assertNotKeepAlive).run

-- RFC 9112 §9.6: a server that sends `close` closes after that response.
#eval checkCases "HTTP/1.0 keep-alive, the handler sets Connection: close" #[
    ("one response, close and no keep-alive", do
      let r ← serveRaw "GET /1 HTTP/1.0\x0d\nConnection: keep-alive\x0d\n\x0d\nGET /2 HTTP/1.0\x0d\nConnection: keep-alive\x0d\n\x0d\n"
        (show TestHandler from fun _ => Response.ok |>.header! "Connection" "close" |>.text "x") (closeInput := true)
      (Want.all [.responses 1, .contains "Connection: close\x0d\n", .absent "keep-alive"]).check r)
  ] (·.2)

/-! ## Connection options (RFC 9110 §7.6.1, §7.8) -/

#eval checkCases "Connection options: machine" #[
    ("§7.8: 426 keeps Connection: upgrade and appends close", do
      -- RFC 9110 §7.6.1, §7.8: the handler's connection options are kept, with the machine's `close`
      MachineTester.receiving "§7.8: 426 keeps Connection: upgrade and appends close"
        |>.feed "GET / HTTP/1.1\r\nHost: example.com\r\nConnection: close\r\n\r\n"
        |>.step |>.assertIsWaitingMessage
        |>.send (upgrade "Upgrade")
        |>.setKnownSize (.fixed 0) |>.userClosedBody |>.step
        |>.assertOutputContains "Connection: upgrade, close\r\n" "expected the handler's upgrade option and close"
        |>.assertOutputContains "Upgrade: TLS/1.2\r\n" "expected the Upgrade field" |>.run),
    ("§7.8: keep-alive response keeps the handler's Connection: upgrade", do
      MachineTester.receiving "§7.8: keep-alive response keeps the handler's Connection: upgrade"
        |>.feed (mkGet "/") |>.step |>.assertKeepAlive
        |>.send (upgrade "upgrade, keep-alive")
        |>.setKnownSize (.fixed 0) |>.userClosedBody |>.step |>.assertKeepAlive
        |>.assertOutputContains "Connection: upgrade\r\n" "expected only the upgrade option" |>.run),
    ("§7.8: client keeps the caller's Connection: upgrade", do
      -- RFC 9110 §7.8: a client that sends `Upgrade` also sends the `upgrade` connection option
      MachineTester.sending "§7.8: client keeps the caller's Connection: upgrade"
        |>.send { minimalGetRequest with
          headers := minimalGetRequest.headers
            |>.insert! "Connection" "Upgrade" |>.insert! "Upgrade" "websocket" }
        |>.userClosedBody |>.step
        |>.assertOutputContains "Connection: upgrade\r\n" "expected the caller's upgrade option"
        |>.assertOutputContains "Upgrade: websocket\r\n" "expected the Upgrade field" |>.run),
    ("§7.8: client appends close to the caller's connection options", do
      MachineTester.sending "§7.8: client appends close to the caller's connection options"
        |>.send { minimalGetRequest with
          headers := minimalGetRequest.headers
            |>.insert! "Connection" "upgrade, close" |>.insert! "Upgrade" "websocket" }
        |>.userClosedBody |>.step |>.assertNotKeepAlive
        |>.assertOutputContains "Connection: upgrade, close\r\n" "expected the upgrade option, then close"
        |>.run)
  ] (·.2)

#eval checkCases "Connection options: async_http_connection_options.lean" #[
    ("for value in ['keep-alive, ', ', keep-alive', 'keep-alive,,'",
      do
        for value in ["keep-alive, ", ", keep-alive", "keep-alive,,", ""] do
          check s!"Connection: {value.quote}"
            (mkGet "/1" s!"Connection: {value}\x0d\n" ++ mkGetClose "/2")
            uriHandler fun r => assertResponseCount r 2),
    ("handler Connection: upgrade,",
      do
        check "handler Connection: upgrade," (mkGetClose "/")
          (fun _ => Response.ok |>.header! "Connection" "upgrade," |>.text "ok")
          fun r => assertContains r "Connection: upgrade, close")
  ] (·.2)

/-! ## Pipelining (RFC 9112 §9.3.2) -/

#eval checkCases "Pipelining: machine" #[
    ("§9.3: pipelining — two requests on one connection", do
      -- §9.3: after completing first request, machine resets and parses second (pipelining)
      let req1 := mkGet "/"
      let req2 := mkGet "/second"
      MachineTester.receiving "§9.3: pipelining — two requests on one connection"
        |>.feed (req1 ++ req2) |>.step |>.assertHasEndHeaders |>.assertKeepAlive
        |>.send { status := .ok } |>.setKnownSize (.fixed 0) |>.userClosedBody
        |>.drainBody |>.step |>.assertHasNext
        |>.step |>.assertHasEndHeaders |>.run),
    ("§9.3: pipelining after CL:0 body — second request path correct", do
      -- §9.3: pipelining after CL:0 body — second request parses correctly
      let post1 := "POST /a HTTP/1.1\r\nHost: example.com\r\nContent-Length: 0\r\n\r\n"
      let get2  := "GET /b HTTP/1.1\r\nHost: example.com\r\n\r\n"
      MachineTester.receiving "§9.3: pipelining after CL:0 body — second request path correct"
        |>.feed (post1 ++ get2) |>.step |>.assertHasEndHeaders
        |>.drainBody |>.assertPulledBody .empty
        |>.send { status := .ok } |>.setKnownSize (.fixed 0) |>.userClosedBody
        |>.step |>.assertHasNext
        |>.step |>.assertHasEndHeaders
        |>.onEndHeaders (fun t head =>
          let path := toString head.uri.path
          if path == "/b" then t
          else t.addError s!"expected second request path /b, got {path}")
        |>.run),
    ("§9.3: resetForNextMessage preserves noMoreInput after pipeline exhausted", do
      -- §9.3: resetForNextMessage must preserve the noMoreInput flag so the machine
      --       halts after the pipeline is exhausted and the socket has closed
      let req1 := mkGet "/first"
      let req2 := mkGet "/second"
      MachineTester.receiving "§9.3: resetForNextMessage preserves noMoreInput after pipeline exhausted"
        |>.feed (req1 ++ req2) |>.noMoreInput
        |>.step |>.assertHasEndHeaders
        |>.send { status := .ok } |>.setKnownSize (.fixed 0) |>.userClosedBody
        |>.drainBody |>.step |>.assertHasNext
        |>.step |>.assertHasEndHeaders
        |>.send { status := .ok } |>.setKnownSize (.fixed 0) |>.userClosedBody
        |>.drainBody |>.step
        |>.assertHasEvent (fun | .close => true | _ => false)
            "expected .close after pipeline exhausted on closed socket"
        |>.step |>.assertHalted |>.run),
    ("RFC 9112 §9.3: HTTP/1.0 keep-alive pipelining — second request parsed", do
      -- §19.7.1: HTTP/1.0 keep-alive allows a second request on the same connection
      let http10req1 := "GET / HTTP/1.0\r\nConnection: keep-alive\r\n\r\n"
      let http10req2 := "GET /second HTTP/1.0\r\n\r\n"
      MachineTester.receiving "RFC 9112 §9.3: HTTP/1.0 keep-alive pipelining — second request parsed"
        |>.feed (http10req1 ++ http10req2) |>.step |>.assertHasEndHeaders |>.assertKeepAlive
        |>.send { status := .ok } |>.setKnownSize (.fixed 0) |>.userClosedBody
        |>.drainBody |>.step |>.assertHasNext
        |>.step |>.assertHasEndHeaders |>.run)
  ] (·.2)

#eval checkCases "Pipelining: async_http_connection_options.lean" #[
    ("Connection: keep-alive",
      do
        -- Control: `keep-alive` alone keeps an HTTP/1.0 connection open.
        check "Connection: keep-alive"
          "GET /1 HTTP/1.0\x0d\nConnection: keep-alive\x0d\n\x0d\nGET /2 HTTP/1.0\x0d\n\x0d\n"
          uriHandler fun r => assertResponseCount r 2)
  ] (·.2)

#eval checkCases "Pipelining: async_http_keepalive.lean" #[
    ("two sequential keep-alive requests → 2 responses",
      do
        check "two sequential keep-alive requests → 2 responses"
          (raw :=
            "GET /first HTTP/1.1\x0d\nHost: example.com\x0d\n\x0d\n" ++
            "GET /second HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")
          (handler := fun req => Response.ok |>.text (toString req.line.uri))
          (expect := fun r =>
            assertResponseCount r 2 *>
            assertContains r "/first" *>
            assertContains r "/second"))
  ] (·.2)

/-! ## Pipelining after a body (RFC 9112 §6.3, §9.3.2) -/

#eval checkCases "Pipelining after a body: async_http_fuzz.lean" #[
    ("fuzz_complete_first_body_allows_pipeline",
      runWithTimeout "fuzz_complete_first_body_allows_pipeline" 20000 do
      fuzzCompleteFirstBodyAllowsPipeline 30 0x00777777)
  ] (·.2)

#eval checkCases "Pipelining after a body: async_http_hang_regressions.lean" #[
    ("10_pipeline_fixed_then_get",
      runWithTimeout "10_pipeline_fixed_then_get" 2000 do
      let raw := ("POST /one HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 5\x0d\n\x0d\nhello" ++
                  "GET /two HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n").toUTF8
      let response ← sendRawTimed "10_pipeline_fixed_then_get/send" raw uriHandler
      assertStatusCount "10_pipeline_fixed_then_get" response 2
      assertContains response "/one"
      assertContains response "/two"),
    ("11_pipeline_chunked_then_get",
      runWithTimeout "11_pipeline_chunked_then_get" 2000 do
      let raw := ("POST /chunk HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n" ++
                  "GET /two HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n").toUTF8
      let response ← sendRawTimed "11_pipeline_chunked_then_get/send" raw uriHandler
      assertStatusCount "11_pipeline_chunked_then_get" response 2
      assertContains response "/chunk"
      assertContains response "/two"),
    ("19_pipeline_large_unread_then_get",
      runWithTimeout "19_pipeline_large_unread_then_get" 2000 do
      let body := String.ofList (List.replicate 5000 'b')
      let raw := (s!"POST /big HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 5000\x0d\n\x0d\n{body}" ++
                  "GET /after HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n").toUTF8
      let response ← sendRawTimed "19_pipeline_large_unread_then_get/send" raw uriHandler
      assertStatusCount "19_pipeline_large_unread_then_get" response 2
      assertContains response "/big"
      assertContains response "/after"),
    ("20_triple_pipeline_mixed",
      runWithTimeout "20_triple_pipeline_mixed" 2000 do
      let raw := ("POST /a HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 4\x0d\n\x0d\ndata" ++
                  "POST /b HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\n\x0d\n3\x0d\nhey\x0d\n0\x0d\n\x0d\n" ++
                  "GET /c HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n").toUTF8
      let response ← sendRawTimed "20_triple_pipeline_mixed/send" raw uriHandler
      assertStatusCount "20_triple_pipeline_mixed" response 3
      assertContains response "/a"
      assertContains response "/b"
      assertContains response "/c")
  ] (·.2)

#eval checkCases "Pipelining after a body: async_http_keepalive.lean" #[
    ("pipelined requests after an exact Content-Length",
      do
        let (response, seen) ← runPipelined
          ("POST /first HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 3\x0d\n\x0d\nabc" ++
           "GET /second HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")

        assertResponseCount response 2
        assertContains response "/first"
        assertContains response "/second"
        assertSeenCount seen 2),
    ("bytes inside a declared body are never parsed as a request",
      do
        let (response1, seen1) ← runPipelined
          ("POST /first HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 10\x0d\n\x0d\nabc" ++
           "GET /second HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")

        assertContains response1 "/first"
        assertAbsent response1 "/second"
        assertSeenCount seen1 1),
    ("broken chunked body stops pipelining",
      do
        let (response2, seen2) ← runPipelined
          ("POST /chunked-first HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\n\x0d\nF\x0d\nhel" ++
           "GET /second HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")

        assertAbsent response2 "/second"
        assertContains response2 "HTTP/1.1 400"
        assertSeenCount seen2 1),
    ("pipelining after Content-Length: 0",
      do
        let (resp1, seen1) ← runPipelined
          ("POST /empty HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 0\x0d\n\x0d\n" ++
           "GET /tail HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")

        assertResponseCount resp1 2
        assertContains resp1 "/empty"
        assertContains resp1 "/tail"
        assertSeenCount seen1 2),
    ("pipelining after a complete chunked body",
      do
        let (resp2, seen2) ← runPipelined
          ("POST /chunked HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n" ++
           "GET /tail HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")

        assertResponseCount resp2 2
        assertContains resp2 "/chunked"
        assertContains resp2 "/tail"
        assertSeenCount seen2 2)
  ] (·.2)

#eval checkCases "Pipelining after a body: server" #[
    ("extra bytes beyond CL become next pipelined request",
      check "extra bytes beyond CL become next pipelined request"
        (raw :=
          "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 5\x0d\n\x0d\nhello" ++
          "GET /second HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")
        (handler := fun req => do
          let body : String ← req.body.readAll
          Response.ok |>.text s!"{toString req.line.uri}:{body}")
        (expect := fun r =>
          assertResponseCount r 2 *>
          assertContains r "/:hello" *>
          assertContains r "/second:" *>
          assertAbsent r "/second:hello"))
  ] (·.2)


-- RFC 9112 §6.3: Content-Length ends the body; what follows is the next request line.
#eval checkCases "Bytes after a Content-Length body" #[
    ("CL 7 with abcdef LF ???", do
      let r ← serveRaw "POST / HTTP/1.1\x0d\nHost: a\x0d\nContent-Length: 7\x0d\n\x0d\nabcdef\n???" echoHandler (closeInput := true)
      let text := String.fromUTF8! r
      ensure (text.startsWith "HTTP/1.1 200" && text.contains "\x0d\n\x0d\nabcdef\n" && text.endsWith r400 &&
        (text.splitOn "HTTP/1.1 ").length == 3) s!"expected 200 with abcdef LF, then 400:\n{text.quote}")
  ] (·.2)

/-! ## Errors end the connection (RFC 9112 §9.6) -/

#eval checkCases "Errors end the connection: async_http_h1_close_with_error.lean" #[
    ("show IO Unit from do",
      show IO Unit from do
      for (name, input) in [
          ("nothing after the request", getRequest),
          ("pipelined request", getRequest ++ "GET /2 HTTP/1.1\r\nHost: a\r\n\r\n"),
          ("stray CRLF", getRequest ++ "\r\n"),
          ("unread body, then a pipelined request",
            "POST / HTTP/1.1\r\nHost: a\r\nContent-Length: 3\r\n\r\nabc" ++ getRequest)] do
        for status in [Status.serviceUnavailable, .requestTimeout] do
          if (stepsToHalt ((streaming input).closeWithError status)).isNone then
            throw <| IO.userError
              s!"'{name}', {status.toCode}: the machine did not halt after closeWithError")
  ] (·.2)

#eval checkCases "Errors end the connection: async_http_h1_framing_mismatch.lean" #[
    ("pipelined request after the 500",
      do
        -- The 500 closes the connection, so a pipelined request gets no answer.
        checkTimed "pipelined request after the 500"
          (raw := getRequest ++ getRequest)
          (handler := fun _ => Response.ok |>.header! "Content-Length" "1234" |>.text "")
          (expect := fun r => do
            let text := String.fromUTF8! r
            unless (text.splitOn "HTTP/1.1 ").length == 2 do
              throw <| IO.userError s!"expected exactly one response, got:\n{text.quote}"))
  ] (·.2)

#eval checkCases "Errors end the connection: async_http_hang_regressions.lean" #[
    ("12_malformed_closes_connection",
      runWithTimeout "12_malformed_closes_connection" 2000 do
      let raw := ("GET / HTTP/1.1\x0d\nHost: example.com\x0d\nBadHeader value\x0d\n\x0d\n" ++
                  "GET /second HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n").toUTF8
      let response ← sendRawTimed "12_malformed_closes_connection/send" raw uriHandler
      assertStatusPrefix "12_malformed_closes_connection" response "HTTP/1.1 400"
      assertStatusCount "12_malformed_closes_connection" response 1)
  ] (·.2)

/-! ## Request count -/

#eval checkCases "Request count: async_http_fuzz_limits.lean" #[
    ("fuzz_max_messages_per_connection",
      runWithTimeout "fuzz_max_messages_per_connection" 30000 do
      fuzzMaxMessagesPerConnection 30 0x00123ABC)
  ] (·.2)

#eval checkCases "Request count: async_http_keepalive.lean" #[
    ("maxRequests: 2 caps third request",
      do
        check "maxRequests: 2 caps third request"
          (raw :=
            "GET /0 HTTP/1.1\x0d\nHost: example.com\x0d\n\x0d\n" ++
            "GET /1 HTTP/1.1\x0d\nHost: example.com\x0d\n\x0d\n" ++
            "GET /2 HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")
          (handler := fun req => Response.ok |>.text (toString req.line.uri))
          (config := { defaultConfig with maxRequests := 2, lingeringTimeout := 3000 })
          (expect := fun r =>
            assertResponseCount r 2 *>
            assertContains r "/0" *>
            assertContains r "/1" *>
            assertAbsent r "/2"))
  ] (·.2)


-- RFC 9112 §9.6: a server that will not reuse the connection says so.
#eval checkCases "enableKeepAlive := false" #[
    ("a 1.1 request gets Connection: close", checkHandler "GET / HTTP/1.1\x0d\nHost: a\x0d\n\x0d\n" okHandler
      (.all [.status "HTTP/1.1 200", .contains "Connection: close\x0d\n"]) { testConfig with enableKeepAlive := false })
  ] (·.2)
