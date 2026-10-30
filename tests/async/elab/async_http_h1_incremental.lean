import Std.Http

open Std Http
open Std.Http.Protocol.H1

private def ensure (name : String) (cond : Bool) (msg : String) : IO Unit := do
  unless cond do
    throw <| IO.userError s!"Test '{name}' failed:\n{msg}"

private def hasFailedEvent (events : Array (Event .receiving)) : Bool :=
  events.any fun
    | .failed _ => true
    | _ => false

private def hasNeedMoreDataEvent (events : Array (Event .receiving)) : Bool :=
  events.any fun
    | .needMoreData _ => true
    | _ => false

private def hasEndHeadersEvent (events : Array (Event .receiving)) : Bool :=
  events.any fun
    | .endHeaders _ => true
    | _ => false

private def hasCloseBodyEvent (events : Array (Event .receiving)) : Bool :=
  events.any fun
    | .closeBody => true
    | _ => false

private def hasContinueEvent (events : Array (Event .receiving)) : Bool :=
  events.any fun
    | .«continue» => true
    | _ => false

private def countNeedAnswerEvents (events : Array (Event .receiving)) : Nat :=
  events.foldl (init := 0) fun n e =>
    match e with
    | .needAnswer => n + 1
    | _ => n

private def countFailedEvents (events : Array (Event .receiving)) : Nat :=
  events.foldl (init := 0) fun n e =>
    match e with
    | .failed _ => n + 1
    | _ => n

private def pulledBodyBytes (chunks : Array PulledChunk) : ByteArray :=
  chunks.foldl (fun acc c => acc ++ c.chunk.data) .empty

private def splitEveryByte (data : ByteArray) : Array ByteArray := Id.run do
  let mut parts : Array ByteArray := #[]
  for i in [0:data.size] do
    parts := parts.push (data.extract i (i + 1))
  parts

private def nextSeed (seed : Nat) : Nat :=
  (1664525 * seed + 1013904223) % 4294967296

private def randBelow (seed : Nat) (maxExclusive : Nat) : Nat × Nat :=
  let seed' := nextSeed seed
  if maxExclusive = 0 then
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
      if r < 26 then 97 + r
      else if r < 36 then 48 + (r - 26)
      else if r = 36 then 45
      else 95
    out := out.push (UInt8.ofNat code)
  (out, s)

private def randomSplit (seed : Nat) (data : ByteArray) (maxPart : Nat := 13) : Array ByteArray × Nat := Id.run do
  let mut s := seed
  let mut out : Array ByteArray := #[]
  let mut i := 0
  while i < data.size do
    let remaining := data.size - i
    let upper := Nat.min maxPart remaining
    let (partLen, s') := randIn s 1 upper
    s := s'
    out := out.push (data.extract i (i + partLen))
    i := i + partLen
  (out, s)

private def randomChunkedPayload (seed : Nat) (body : ByteArray) : ByteArray × Nat := Id.run do
  let mut s := seed
  let mut out := ByteArray.empty
  let mut i := 0
  while i < body.size do
    let remaining := body.size - i
    let upper := Nat.min 9 remaining
    let (chunkLen, s') := randIn s 1 upper
    s := s'
    out := out ++ s!"{chunkLen}\r\n".toUTF8
    out := out ++ body.extract i (i + chunkLen)
    out := out ++ "\r\n".toUTF8
    i := i + chunkLen
  out := out ++ "0\r\n\r\n".toUTF8
  (out, s)

private def mkContentLengthRequest (path : String) (body : ByteArray) : ByteArray :=
  s!"POST {path} HTTP/1.1\r\nHost: example.com\r\nContent-Length: {body.size}\r\nConnection: keep-alive\r\n\r\n".toUTF8 ++ body

private def mkChunkedRequest (path : String) (chunkedPayload : ByteArray) : ByteArray :=
  s!"POST {path} HTTP/1.1\r\nHost: example.com\r\nTransfer-Encoding: chunked\r\nConnection: keep-alive\r\n\r\n".toUTF8 ++ chunkedPayload

private def mkChunkedHead (path : String) : ByteArray :=
  s!"POST {path} HTTP/1.1\r\nHost: example.com\r\nTransfer-Encoding: chunked\r\nConnection: keep-alive\r\n\r\n".toUTF8

private structure IncrementalTrace where
  machine : Machine .receiving
  events : Array (Event .receiving) := #[]
  output : ByteArray := .empty
  pulled : Array PulledChunk := #[]

private def runIncrementalReceiving
    (parts : Array ByteArray)
    (config : Protocol.H1.Config := {}) : IncrementalTrace := Id.run do
  let mut machine : Machine .receiving := { config := config }
  let mut events : Array (Event .receiving) := #[]
  let mut output := ByteArray.empty
  let mut pulled : Array PulledChunk := #[]

  for part in parts do
    machine := machine.feed part
    let (machine', step) := machine.step
    machine := machine'
    events := events ++ step.events
    output := output ++ step.output.toByteArray

    -- Pull at most one body chunk per input part to simulate streaming callers.
    -- Guard on buffered bytes to avoid calling into body parsing on an empty buffer.
    if machine.canPullBodyNow && machine.reader.input.remainingBytes > 0 then
      let (machine', pulledNow?) := machine.pullBody
      let (machine', pullEvents) := machine'.takeEvents
      machine := machine'
      if let some pulledNow := pulledNow? then
        pulled := pulled.push pulledNow
      events := events ++ pullEvents
    else
      pure ()

  let (machine', finalStep) := machine.step
  machine := machine'
  events := events ++ finalStep.events
  output := output ++ finalStep.output.toByteArray

  -- After all input has arrived, drain the remaining ready body chunks.
  let mut fuel := 4096
  while fuel > 0 && machine.canPullBodyNow && machine.reader.input.remainingBytes > 0 do
    fuel := fuel - 1
    let (machine', pulledNow?) := machine.pullBody
    let (machine', pullEvents) := machine'.takeEvents
    machine := machine'
    events := events ++ pullEvents
    match pulledNow? with
    | some pulledNow =>
        pulled := pulled.push pulledNow
    | none =>
        break

  return { machine, events, output, pulled }

private def assertIncrementalSuccess
    (name : String)
    (trace : IncrementalTrace)
    (expectedBody : ByteArray)
    (expectNeedMoreData : Bool := true) : IO Unit := do
  ensure name (!trace.machine.failed) s!"machine ended failed with events:\n{repr trace.events}"
  ensure name (!hasFailedEvent trace.events) s!"unexpected failure events:\n{repr trace.events}"
  ensure name (hasEndHeadersEvent trace.events) s!"missing endHeaders event:\n{repr trace.events}"

  if expectNeedMoreData then
    ensure name (hasNeedMoreDataEvent trace.events) s!"expected at least one needMoreData event:\n{repr trace.events}"
  else
    pure ()

  let got := pulledBodyBytes trace.pulled
  ensure name (got == expectedBody)
    s!"body mismatch:\nexpected={String.fromUTF8! expectedBody |>.quote}\nactual={String.fromUTF8! got |>.quote}"

  let expectsPullSignals := expectedBody.size > 0 || trace.pulled.size > 0
  if expectsPullSignals then
    ensure name (hasCloseBodyEvent trace.events) s!"missing closeBody event:\n{repr trace.events}"
    ensure name (trace.pulled.any (·.final)) "expected at least one final pulled chunk"
    ensure name ((trace.pulled.back?.map (·.final)).getD false) "expected last pulled chunk to be final"
  else
    pure ()

private def runOneStepReceiving
    (payload : ByteArray)
    (config : Protocol.H1.Config := {}) :
    Machine .receiving × StepResult .receiving :=
  let machine0 : Machine .receiving := { config := config }
  (machine0.feed payload).step

private def assertFailedWith
    (name : String)
    (payload : ByteArray)
    (expected : Error)
    (config : Protocol.H1.Config := {}) : IO Unit := do
  let (machine, step) := runOneStepReceiving payload config
  ensure name (hasFailedEvent step.events) s!"expected failure event, events:\n{repr step.events}"
  ensure name (machine.error == some expected)
    s!"expected error {repr expected}, got {repr machine.error}"

-- Deterministic: one-byte incremental content-length request.
#eval show IO Unit from do
  let body := "hello".toUTF8
  let request := mkContentLengthRequest "/inc-every-byte" body
  let trace := runIncrementalReceiving (splitEveryByte request)
  assertIncrementalSuccess "CL one-byte incremental parse" trace body

-- Deterministic: fragmented chunked request with boundaries through chunk metadata and payload.
#eval show IO Unit from do
  let body := "abcXYZ".toUTF8
  let payload := "3\r\nabc\r\n3\r\nXYZ\r\n0\r\n\r\n".toUTF8
  let request := mkChunkedRequest "/inc-chunked" payload
  let parts : Array ByteArray := #[
    request.extract 0 17,
    request.extract 17 39,
    request.extract 39 58,
    request.extract 58 (request.size - 4),
    request.extract (request.size - 4) request.size
  ]
  let trace := runIncrementalReceiving parts
  assertIncrementalSuccess "Chunked fragmented parse" trace body

-- Regression: calling `pullBody` in chunked mode before any chunk-size byte arrives
-- must request more data rather than failing the machine.
#eval show IO Unit from do
  let headOnly := mkChunkedHead "/wait-for-chunk-size"
  let machine0 : Machine .receiving := { config := {} }
  let (machine1, step1) := (machine0.feed headOnly).step
  ensure "Chunked pull on empty input (setup)" (!machine1.failed) s!"unexpected setup failure events:\n{repr step1.events}"
  ensure "Chunked pull on empty input (setup)" (hasEndHeadersEvent step1.events) "expected endHeaders in setup"
  ensure "Chunked pull on empty input (setup)" machine1.canPullBodyNow "expected body state to be pullable"

  let (machine2, pulled?) := machine1.pullBody
  let (machine2, pullEvents) := machine2.takeEvents

  ensure "Chunked pull on empty input" pulled?.isNone "expected no pulled body chunk"
  ensure "Chunked pull on empty input" (!machine2.failed) s!"unexpected machine failure:\n{repr pullEvents}"
  ensure "Chunked pull on empty input" (hasNeedMoreDataEvent pullEvents)
    s!"expected needMoreData after empty pull:\n{repr pullEvents}"

-- Regression: unread buffered input must stay bounded to avoid memory blowups
-- when upper layers stall request-body consumption.
#eval show IO Unit from do
  let cfg : Protocol.H1.Config := {
    maxBodySize := 32
    maxHeaderBytes := 16
    maxStartLineLength := 16
    maxChunkLineLength := 16
  }
  let cap := cfg.maxBodySize + cfg.maxHeaderBytes + cfg.maxStartLineLength + cfg.maxChunkLineLength
  let payload := ByteArray.mk (Array.replicate (cap + 1) (UInt8.ofNat 97))
  let machine0 : Machine .receiving := { config := cfg }
  let machine1 := machine0.feed payload

  ensure "Buffered input cap triggers failure" machine1.failed "expected machine to fail on oversized buffered input"
  ensure "Buffered input cap triggers entityTooLarge" (machine1.error == some .entityTooLarge)
    s!"expected entityTooLarge failure, got {repr machine1.error}"

-- Property-style: randomized content-length body and randomized split boundaries.
#eval show IO Unit from do
  let mut seed : Nat := 0x21436587
  for i in [0:120] do
    let (bodyLen, s1) := randIn seed 0 128
    seed := s1
    let (body, s2) := randomAsciiBytes seed bodyLen
    seed := s2

    let request := mkContentLengthRequest s!"/prop-cl-{i}" body
    let (parts, s3) := randomSplit seed request 11
    seed := s3

    let trace := runIncrementalReceiving parts
    assertIncrementalSuccess s!"Property CL #{i}" trace body (expectNeedMoreData := parts.size > 1)

-- Property-style: randomized chunked payload and randomized split boundaries.
#eval show IO Unit from do
  let mut seed : Nat := 0x89abcdef
  for i in [0:120] do
    let (bodyLen, s1) := randIn seed 0 128
    seed := s1
    let (body, s2) := randomAsciiBytes seed bodyLen
    seed := s2

    let (payload, s3) := randomChunkedPayload seed body
    seed := s3
    let request := mkChunkedRequest s!"/prop-chunked-{i}" payload
    let (parts, s4) := randomSplit seed request 9
    seed := s4

    let trace := runIncrementalReceiving parts
    assertIncrementalSuccess s!"Property chunked #{i}" trace body (expectNeedMoreData := parts.size > 1)

private def getEndHeadersHead (events : Array (Event .receiving)) : Option Request.Head :=
  events.findSome? fun
    | .endHeaders head => some head
    | _ => none
