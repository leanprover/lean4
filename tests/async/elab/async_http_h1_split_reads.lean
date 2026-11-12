module

import Std.Http.Test.Helpers
import Std.Http.Test.Machine

/-!
# HTTP/1.1 split reads

A request reads the same however its bytes are split into reads: every method, bodies, chunk
extensions and trailers, an overlong target, and random splits through `serveConnection`. RFC 9112
§3, §6.3, §7.1. Regressions: #15841, #16080, #16111.
-/

open Std Http
open Std.Async
open Std.Http.Protocol.H1
open Std.Http.Internal.Test

private def mkContentLengthRequest (path : String) (body : ByteArray) : ByteArray :=
  s!"POST {path} HTTP/1.1\r\nHost: example.com\r\nContent-Length: {body.size}\r\nConnection: keep-alive\r\n\r\n".toUTF8 ++ body

private def mkChunkedRequest (path : String) (chunkedPayload : ByteArray) : ByteArray :=
  s!"POST {path} HTTP/1.1\r\nHost: example.com\r\nTransfer-Encoding: chunked\r\nConnection: keep-alive\r\n\r\n".toUTF8 ++ chunkedPayload

private def mkChunkedHead (path : String) : ByteArray :=
  s!"POST {path} HTTP/1.1\r\nHost: example.com\r\nTransfer-Encoding: chunked\r\nConnection: keep-alive\r\n\r\n".toUTF8

private def randIn (g : Rng) (low high : Nat) : Nat × Rng :=
  if high < low then (low, g) else
    let (n, g) := g.below (high - low + 1)
    (low + n, g)

/-- Lowercase letters, digits, `-` and `_`. -/
private def randomAsciiBytes (g : Rng) (len : Nat) : ByteArray × Rng := Id.run do
  let mut g := g
  let mut out := ByteArray.empty
  for _ in [0:len] do
    let (r, g') := g.below 38
    g := g'
    let code := if r < 26 then 97 + r else if r < 36 then 48 + (r - 26) else if r = 36 then 45 else 95
    out := out.push (UInt8.ofNat code)
  (out, g)

private def randomSplit (g : Rng) (data : ByteArray) (maxPart : Nat) : Array ByteArray × Rng := Id.run do
  let mut g := g
  let mut out : Array ByteArray := #[]
  let mut i := 0
  while i < data.size do
    let (partLen, g') := randIn g 1 (Nat.min maxPart (data.size - i))
    g := g'
    out := out.push (data.extract i (i + partLen))
    i := i + partLen
  (out, g)

private def randomChunkedPayload (g : Rng) (body : ByteArray) : ByteArray × Rng := Id.run do
  let mut g := g
  let mut out := ByteArray.empty
  let mut i := 0
  while i < body.size do
    let (chunkLen, g') := randIn g 1 (Nat.min 9 (body.size - i))
    g := g'
    out := out ++ s!"{chunkLen}\r\n".toUTF8 ++ body.extract i (i + chunkLen) ++ "\r\n".toUTF8
    i := i + chunkLen
  (out ++ "0\r\n\r\n".toUTF8, g)

/-- What the pull-only cases checked: the head was read, the body is `want`, and its last chunk is final. -/
private def expectPullOnly (t : Trace) (want : ByteArray) : IO Unit := do
  ensure (t.events.any (· matches .endHeaders _)) s!"missing endHeaders event:\n{repr t.events}"
  ensure (t.body == want)
    s!"body mismatch:\nexpected={(String.fromUTF8? want).getD "<binary>" |>.quote}\nactual={(String.fromUTF8? t.body).getD "<binary>" |>.quote}"
  ensure ((t.pulled.back?.map (·.final)).getD false) "expected last pulled chunk to be final"

/-- Sends `parts` one at a time to `serveConnection`, then EOF, and returns what it wrote. -/
private def serveParts (parts : Array ByteArray) (handler : TestHandler) : IO ByteArray := do
  let (client, server) ← Internal.Mock.new
  Async.block do
    let serverTask ← async (t := AsyncTask) do
      Server.serveConnection server handler testConfig |>.run
    for part in parts do
      client.send part
    client.getSendChan.close
    await serverTask
    return (← client.recv?).getD .empty

/-- The first response's content, as the echo handler wrote it. -/
private def responseBody (response : ByteArray) : String :=
  match ((String.fromUTF8! response).splitOn "\x0d\n\x0d\n").drop 1 with
  | [] => ""
  | body :: _ => body

/-! ## Methods (RFC 9112 §3) -/

-- The method is read whole before it is matched, so the outcome does not depend on where a read
-- ends inside it (#16111: `UPDATE` must not match the start of `UPDATEREDIRECTREF`).
#eval checkCases "methods across split reads" #[
    ("every method, split after each byte", do
      for expected in Method.all do
        let name := toString expected
        unless Method.ofString? name == some expected do
          throw <| IO.userError s!"Method.ofString? {name.quote} is not {repr expected}"
        let (target, host) := if name == "CONNECT" then ("example.com:443", "example.com:443") else ("/", "example.com")
        let request := s!"{name} {target} HTTP/1.1\r\nHost: {host}\r\n\r\n".toUTF8
        for i in [1:name.length + 2] do
          MachineTester.receiving s!"§3: {name} split after byte {i}"
            |>.feedBytes (request.extract 0 i) |>.step |>.assertNoError
            |>.feedBytes (request.extract i request.size) |>.step |>.assertNoError
            |>.onEndHeaders (fun t head =>
              if head.method == expected then t else t.addError s!"expected {name}, got {repr head.method}")
            |>.run),
    ("unrecognized methods split after each byte → unsupportedMethod (#16111)", do
      for method in ["LEAN", "GETX", "UPDATEX", "UPDATEREDIRECTREFS"] do
        let request := s!"{method} / HTTP/1.1\r\nHost: example.com\r\n\r\n".toUTF8
        for i in [1:method.length + 1] do
          MachineTester.receiving s!"§3: unrecognized {method} split after byte {i} → unsupportedMethod"
            |>.feedBytes (request.extract 0 i) |>.step |>.assertNoError
            |>.feedBytes (request.extract i request.size) |>.step
            |>.assertFailedWith .unsupportedMethod |>.run)
  ] (·.2)

/-! ## Bodies (RFC 9112 §6.3, §7.1) -/

-- The same request reads the same at every single split point, one byte per read, and with the
-- pull-only driver (the head stepped once, then the body fed and pulled without stepping).
#eval checkCases "Content-Length body across reads (#15841)" #[
    ("CL one-byte incremental parse", do
      let body := "hello".toUTF8
      expectBody (feedEachByte (mkContentLengthRequest "/inc-every-byte" body)) body),
    ("CL split at every offset", do
      let body := "hello".toUTF8
      let request := mkContentLengthRequest "/inc-every-split" body
      for i in [1:request.size] do
        try expectBody (feedSplit request i) body (needMoreData := false)
        catch e => throw <| IO.userError s!"split at {i}: {e}"),
    ("§6.3: fixed-length body assembled across incremental feeds (pull only), every body split", do
      let head := "POST / HTTP/1.1\r\nHost: example.com\r\nContent-Length: 5\r\n\r\n".toUTF8
      let body := "hello".toUTF8
      for i in [1:body.size] do
        try expectPullOnly (feedPullOnly #[head, body.extract 0 i, body.extract i body.size] (drainLast := true)) body
        catch e => throw <| IO.userError s!"body split at {i}: {e}")
  ] (·.2)

#eval checkCases "chunked body across reads" #[
    ("Chunked parse at every split point", do
      let request := mkChunkedRequest "/inc-chunked" "3\r\nabc\r\n3\r\nXYZ\r\n0\r\n\r\n".toUTF8
      for i in [1:request.size] do
        try expectBody (feedSplit request i) "abcXYZ".toUTF8 (needMoreData := false)
        catch e => throw <| IO.userError s!"split at {i}: {e}"),
    ("Chunked one-byte incremental parse", do
      let request := mkChunkedRequest "/inc-chunked" "3\r\nabc\r\n3\r\nXYZ\r\n0\r\n\r\n".toUTF8
      expectBody (feedEachByte request) "abcXYZ".toUTF8),
    ("§7.1: chunked body assembled across incremental feeds (pull only), every body split", do
      let head := "POST / HTTP/1.1\r\nHost: example.com\r\nTransfer-Encoding: chunked\r\n\r\n".toUTF8
      let chunked := "5\r\nhello\r\n0\r\n\r\n".toUTF8
      for i in [1:chunked.size] do
        try expectPullOnly (feedPullOnly #[head, chunked.extract 0 i, chunked.extract i chunked.size] (drainLast := true)) "hello".toUTF8
        catch e => throw <| IO.userError s!"body split at {i}: {e}")
  ] (·.2)

-- Calling `pullBody` in chunked mode before any chunk-size byte arrives must request more data
-- rather than failing the machine.
#eval checkCases "Chunked pull on empty input" #[
    ("Chunked pull on empty input", do
      let machine0 : Machine .receiving := { config := {} }
      let (machine1, step1) := (machine0.feed (mkChunkedHead "/wait-for-chunk-size")).step
      ensure (!machine1.failed) s!"unexpected setup failure events:\n{repr step1.events}"
      ensure (step1.events.any (· matches .endHeaders _)) "expected endHeaders in setup"
      ensure machine1.canPullBodyNow "expected body state to be pullable"
      let (machine2, pulled?) := machine1.pullBody
      let (machine2, pullEvents) := machine2.takeEvents
      ensure pulled?.isNone "expected no pulled body chunk"
      ensure (!machine2.failed) s!"unexpected machine failure:\n{repr pullEvents}"
      ensure (pullEvents.any (· matches .needMoreData _)) s!"expected needMoreData after empty pull:\n{repr pullEvents}")
  ] (·.2)

#eval checkCases "Property-style: random bodies and random split boundaries" #[
    ("Property CL", do
      let mut g : Rng := ⟨0x21436587⟩
      for i in [0:120] do
        let (bodyLen, g1) := randIn g 0 128
        let (body, g2) := randomAsciiBytes g1 bodyLen
        let (parts, g3) := randomSplit g2 (mkContentLengthRequest s!"/prop-cl-{i}" body) 11
        g := g3
        try expectBody (feedParts parts) body (needMoreData := parts.size > 1)
        catch e => throw <| IO.userError s!"Property CL #{i}: {e}"),
    ("Property chunked", do
      let mut g : Rng := ⟨0x89abcdef⟩
      for i in [0:120] do
        let (bodyLen, g1) := randIn g 0 128
        let (body, g2) := randomAsciiBytes g1 bodyLen
        let (payload, g3) := randomChunkedPayload g2 body
        let (parts, g4) := randomSplit g3 (mkChunkedRequest s!"/prop-chunked-{i}" payload) 9
        g := g4
        try expectBody (feedParts parts) body (needMoreData := parts.size > 1)
        catch e => throw <| IO.userError s!"Property chunked #{i}: {e}")
  ] (·.2)


private def clientGet : Request.Head :=
  { method := .get, version := .v11, uri := RequestTarget.originForm! "/",
    headers := Headers.empty.insert! "Host" "example.com" }

/-- A client machine that sent a GET, then read `parts` one per step, pulling the body as it came. -/
private def clientReads (parts : Array ByteArray) : Machine .sending × Array (Event .sending) × ByteArray := Id.run do
  let mut m : Machine .sending := { config := {} }
  m := (m.send clientGet |>.userClosedBody).step.1
  let mut events : Array (Event .sending) := #[]
  let mut body := ByteArray.empty
  for part in parts ++ #[ByteArray.empty] do
    m := m.feed part
    let (m', r) := m.step
    m := m'
    events := events ++ r.events
    let mut fuel := 64
    while fuel > 0 && m.canPullBodyNow do
      fuel := fuel - 1
      let (m', c?) := m.pullBody
      let (m', evs) := m'.takeEvents
      m := m'
      events := events ++ evs
      if let some c := c? then body := body ++ c.chunk.data
  return (m, events, body)

-- RFC 9112 §4: a client reads a response the same way whatever its read boundaries.
#eval checkCases "Client: incomplete responses fed one byte at a time" #[
    "HTTP/1.1", "HTTP/1.1 200", "HTTP/1.1 200 OK\x0d\nContent-Length: 2\x0d\n"
  ] fun raw => do
    let (m, events, _) := clientReads (eachByte raw.toUTF8)
    ensure (!m.failed && !events.any (· matches .failed _)) s!"failed: {repr events}"
    ensure (!events.any (· matches .endHeaders _)) s!"a head was read: {repr events}"
    ensure (events.any (· matches .needMoreData _)) s!"no needMoreData: {repr events}"

#eval checkCases "Client: a chunked response with trailers, one byte at a time" #[
    ("same result as one read", do
      let raw := "HTTP/1.1 200 OK\x0d\nTransfer-Encoding: chunked\x0d\n\x0d\n5\x0d\nhello\x0d\n6\x0d\n world\x0d\n0\x0d\nX-T: v\x0d\n\x0d\n".toUTF8
      let (m1, e1, b1) := clientReads #[raw]
      let (m2, e2, b2) := clientReads (eachByte raw)
      for (m, events, body, how) in [(m1, e1, b1, "one read"), (m2, e2, b2, "byte by byte")] do
        ensure (!m.failed && !events.any (· matches .failed _)) s!"{how}: failed: {repr events}"
        ensure (events.any (· matches .endHeaders _)) s!"{how}: no endHeaders: {repr events}"
        ensure (body == "hello world".toUTF8) s!"{how}: body {(String.fromUTF8! body).quote}"
        ensure (m.reader.isComplete || events.any (· matches .closeBody)) s!"{how}: not complete: {repr events}"
      ensure (e2.any (· matches .needMoreData _)) s!"byte by byte: no needMoreData: {repr e2}")
  ] (·.2)

/-! ## Chunk extensions and trailers (RFC 9112 §7.1.1, §7.1.2) -/

-- A read boundary inside a chunk extension or a trailer field must not fail a valid request (#15841).
#eval checkCases "Chunk extension one-byte incremental parse (#15841)" #[
    "5;a=b\r\nhello\r\n0\r\n\r\n", "5 ; a = b\r\nhello\r\n0\r\n\r\n", "5;a=\"b c\"\r\nhello\r\n0\r\n\r\n",
    "5\r\nhello\r\n0;a\r\n\r\n"
  ] fun payload => expectBody (feedEachByte (mkChunkedRequest "/inc-chunk-ext" payload.toUTF8)) "hello".toUTF8

#eval checkCases "Trailers across reads" #[
    ("Trailer one-byte incremental parse (#15841)", do
      let request := mkChunkedRequest "/inc-trailer" "5\r\nhello\r\n0\r\nX-T: a\r\nY: b\r\n\r\n".toUTF8
      expectBody (feedEachByte request) "hello".toUTF8),
    -- After a read that ends inside the second field, only that field is still buffered, so the
    -- next read does not parse the first one again.
    ("Trailer fields consumed one at a time", do
      let input := "5\r\nhello\r\n0\r\nX-A: 1\r\nX-B: 2"
      let trace := feedParts #[mkChunkedRequest "/inc-trailer-fields" input.toUTF8]
      ensure (!trace.machine.failed) s!"machine ended failed with events:\n{repr trace.events}"
      ensure (trace.machine.reader.state matches .readBody (.trailers _ 1))
        s!"unexpected reader state {repr trace.machine.reader.state}"
      ensure (trace.machine.reader.input.remainingBytes == "X-B: 2".length)
        s!"expected only the incomplete field buffered, got {trace.machine.reader.input.remainingBytes} bytes"),
    ("Trailers at the count limit, one byte per read", do
      let atLimit := mkChunkedRequest "/inc-trailer-limit" "5\r\nhello\r\n0\r\nA: 1\r\nB: 2\r\n\r\n".toUTF8
      expectBody (feedEachByte atLimit { maxTrailerHeaders := 2 }) "hello".toUTF8),
    ("Trailers over the count limit, one byte per read", do
      let overLimit := mkChunkedRequest "/inc-trailer-limit" "5\r\nhello\r\n0\r\nA: 1\r\nB: 2\r\nC: 3\r\n\r\n".toUTF8
      let trace := feedEachByte overLimit { maxTrailerHeaders := 2 }
      ensure (trace.machine.error == some .badMessage) s!"expected badMessage, got {repr trace.machine.error}"),
    ("Forbidden trailer field, one byte per read", do
      let forbidden := mkChunkedRequest "/inc-trailer-forbidden" "5\r\nhello\r\n0\r\nA: 1\r\nContent-Length: 5\r\n\r\n".toUTF8
      let trace := feedEachByte forbidden
      ensure (trace.machine.error == some .badMessage) s!"expected badMessage, got {repr trace.machine.error}")
  ] (·.2)

/-! ## Target limit (RFC 9112 §3) -/

-- A request-target longer than `maxUriLength` gets `uriTooLong` however the request line is split
-- into reads, including reads that end between `maxStartLineLength` bytes and the parser's
-- `maxUriLength` check (#16080).
#eval checkCases "Overlong request-target (#16080)" #[
    ("unsplit", 0), ("split at 8191", 8191), ("split at 8192", 8192), ("split at 8193", 8193),
    ("split at 8194", 8194), ("split at 8195", 8195), ("split at 8196", 8196), ("split at 8197", 8197)
  ] fun (label, k) => do
    let request := s!"GET /{String.ofList (List.replicate 8193 'a')} HTTP/1.1\r\nHost: a\r\n\r\n".toUTF8
    let parts := if k == 0 then #[request] else #[request.extract 0 k, request.extract k request.size]
    let trace := feedParts parts
    ensure (trace.machine.error == some .uriTooLong) s!"{label}: expected uriTooLong, got {repr trace.machine.error}"

/-! ## Pipelined streams (RFC 9112 §9.3.2) -/

-- `Reader.feed` keeps the unread bytes, drops the read ones and appends the new data.
#eval checkCases "`Reader.feed` keeps unread bytes" #[
    ("every position and data", do
      for pos in [0:7] do
        for data in ["", "x", "ghij"] do
          let reader : Reader .receiving := { input := ⟨"abcdef".toUTF8, pos⟩ }
          let fed := reader.feed data.toUTF8
          let expected := ("abcdef".toUTF8.extract pos 6) ++ data.toUTF8
          let got := fed.input.array.extract fed.input.pos fed.input.array.size
          ensure (got == expected) s!"feed at {pos} with {data}: got {String.fromUTF8! got}, expected {String.fromUTF8! expected}")
  ] (·.2)


private def requestLine : TestHandler := fun req => do
  let body : String ← req.body.readAll
  Response.ok |>.text s!"{req.line.method} {toString req.line.uri} {body}"

/-- The server machine's view of `parts`: each request's method, target and body, in order. A 200
with an empty body answers each request once its body is read. -/
private def machineReads (parts : Array ByteArray) : Array String × Bool := Id.run do
  let mut m : Machine .receiving := { config := {} }
  let mut seen : Array String := #[]
  let mut current : Option (String × ByteArray) := none
  for part in parts ++ Array.replicate 8 ByteArray.empty do
    m := m.feed part
    let (m', r) := m.step
    m := m'
    for e in r.events do
      if let .endHeaders head := e then
        current := some (s!"{head.method} {toString head.uri}", .empty)
    let mut fuel := 64
    while fuel > 0 && m.canPullBodyNow do
      fuel := fuel - 1
      let (m', c?) := m.pullBody
      m := m'.takeEvents.1
      if let (some c, some (line, body)) := (c?, current) then
        current := some (line, body ++ c.chunk.data)
    if let some (line, body) := current then
      if m.reader.isComplete then
        seen := seen.push s!"{line} {String.fromUTF8! body}"
        current := none
        m := m.send { status := .ok } |>.setKnownSize (.fixed 0) |>.userClosedBody
  return (seen, m.failed)

-- RFC 9112 §9.3.2: a read boundary inside the *next* request does not change either request.
#eval checkCases "A CL POST then a GET, split at every offset" #[
    ("machine", do
      let raw := "POST /a HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 5\x0d\n\x0d\nhelloGET /b HTTP/1.1\x0d\nHost: example.com\x0d\n\x0d\n".toUTF8
      for i in [0:raw.size + 1] do
        let (seen, failed) := machineReads (splitAt raw i)
        ensure (!failed && seen == #["POST /a hello", "GET /b "]) s!"split at {i}: {repr seen} failed={failed}"),
    ("serveConnection", do
      let raw := "POST /a HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 5\x0d\n\x0d\nhelloGET /b HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
      for i in [0:raw.size + 1] do
        let text := String.fromUTF8! (← serveParts (splitAt raw i) requestLine)
        let bodies := (text.splitOn "HTTP/1.1 200 OK").drop 1 |>.map fun r => ((r.splitOn "\x0d\n\x0d\n").drop 1).headD ""
        ensure (bodies == ["POST /a hello", "GET /b "]) s!"split at {i}: {text.quote}")
  ] (·.2)

/-! ## Through serveConnection (RFC 9112 §6.3, §7.1) -/

#eval checkCases "Random bodies through serveConnection" #[
    ("Content-Length body, head whole, body in random 1–17-byte reads", do
      let mut g : Rng := ⟨0x00C0FFEE⟩
      for i in [0:40] do
        let (len, g1) := randIn g 0 128
        let (body, g2) := randomAsciiBytes g1 len
        let head := s!"POST /fuzz-cl-{i} HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: {body.size}\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
        let (bodyParts, g3) := randomSplit g2 body 17
        g := g3
        let response ← serveParts (#[head] ++ bodyParts) echoHandler
        ensure ((String.fromUTF8! response).startsWith "HTTP/1.1 200") s!"fuzz_content_length_echo case={i}: status"
        ensure (responseBody response == String.fromUTF8! body) s!"fuzz_content_length_echo case={i}: body"),
    ("chunked body in random 1–9-byte chunks, sent in random 1–17-byte reads", do
      let mut g : Rng := ⟨0x00123456⟩
      for i in [0:40] do
        let (len, g1) := randIn g 0 128
        let (body, g2) := randomAsciiBytes g1 len
        let (chunked, g3) := randomChunkedPayload g2 body
        g := g3
        let head := s!"POST /fuzz-chunked-{i} HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
        let (parts, g4) := randomSplit g (head ++ chunked) 17
        g := g4
        let response ← serveParts parts echoHandler
        ensure ((String.fromUTF8! response).startsWith "HTTP/1.1 200") s!"fuzz_chunked_echo case={i}: status"
        ensure (responseBody response == String.fromUTF8! body) s!"fuzz_chunked_echo case={i}: body")
  ] (·.2)
