import Std.Internal.Http
import Std.Internal.Async
import Std.Internal.Async.Timer

open Std.Internal.IO Async
open Std Http

abbrev TestHandler := Request Body.Incoming → ContextAsync (Response Body.AnyBody)

instance : Std.Http.Server.Handler TestHandler where
  onRequest handler request := handler request

instance : Coe (ContextAsync (Response Body.Incoming)) (ContextAsync (Response Body.AnyBody)) where
  coe action := do
    let response ← action
    pure { response with body := Body.Internal.incomingToOutgoing response.body }

instance : Coe (Async (Response Body.Incoming)) (ContextAsync (Response Body.AnyBody)) where
  coe action := do
    let response ← action
    pure { response with body := Body.Internal.incomingToOutgoing response.body }


def defaultConfig : Config :=
  { lingeringTimeout := 1000, generateDate := false }


def bad400 : String :=
  "HTTP/1.1 400 Bad Request\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"


def runWithTimeout {α : Type} (name : String) (timeoutMs : Nat := 15000) (action : IO α) : IO α := do
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
        throw <| IO.userError s!"Test '{name}' timed out after {timeoutMs}ms (possible hang/regression)"
      | n + 1 =>
        IO.sleep 10
        loop n

  loop ticks


def sendRaw
    (client : Mock.Client)
    (server : Mock.Server)
    (raw : ByteArray)
    (handler : TestHandler)
    (config : Config := defaultConfig) : IO ByteArray := Async.block do
  client.send raw
  Std.Http.Server.serveConnection server handler config
    |>.run
  let res ← client.recv?
  pure (res.getD .empty)


def sendRawAndClose
    (client : Mock.Client)
    (server : Mock.Server)
    (raw : ByteArray)
    (handler : TestHandler)
    (config : Config := defaultConfig) : IO ByteArray := Async.block do
  client.send raw
  client.getSendChan.close
  Std.Http.Server.serveConnection server handler config
    |>.run
  let res ← client.recv?
  pure (res.getD .empty)


def sendFragmentedAndClose
    (client : Mock.Client)
    (server : Mock.Server)
    (parts : Array ByteArray)
    (handler : TestHandler)
    (config : Config := defaultConfig) : IO ByteArray := Async.block do
  let serverTask ← async (t := AsyncTask) do
    Std.Http.Server.serveConnection server handler config
      |>.run

  for part in parts do
    client.send part

  client.getSendChan.close
  await serverTask

  let res ← client.recv?
  pure (res.getD .empty)


def responseText (response : ByteArray) : String :=
  String.fromUTF8! response


def responseBody (response : ByteArray) : String :=
  let parts := (responseText response).splitOn "\x0d\n\x0d\n"
  match parts.drop 1 with
  | [] => ""
  | body :: _ => body


def assertStatusPrefix (name : String) (response : ByteArray) (prefix_ : String) : IO Unit := do
  let text := responseText response
  unless text.startsWith prefix_ do
    throw <| IO.userError s!"Test '{name}' failed:\nExpected status prefix {prefix_.quote}\nGot:\n{text.quote}"


def assertExact (name : String) (response : ByteArray) (expected : String) : IO Unit := do
  let text := responseText response
  if text != expected then
    throw <| IO.userError s!"Test '{name}' failed:\nExpected:\n{expected.quote}\nGot:\n{text.quote}"


def countOccurrences (s : String) (needle : String) : Nat :=
  if needle.isEmpty then
    0
  else
    (s.splitOn needle).length - 1


def assertStatusCount (name : String) (response : ByteArray) (expected : Nat) : IO Unit := do
  let text := responseText response
  let got := countOccurrences text "HTTP/1.1 "
  if got != expected then
    throw <| IO.userError s!"Test '{name}' failed:\nExpected {expected} responses but saw {got}\n{text.quote}"


def nextSeed (seed : Nat) : Nat :=
  (1664525 * seed + 1013904223) % 4294967296


def randBelow (seed : Nat) (maxExclusive : Nat) : Nat × Nat :=
  let seed' := nextSeed seed
  if maxExclusive == 0 then
    (0, seed')
  else
    (seed' % maxExclusive, seed')


def randIn (seed : Nat) (low : Nat) (high : Nat) : Nat × Nat :=
  if high < low then
    (low, seed)
  else
    let (n, seed') := randBelow seed (high - low + 1)
    (low + n, seed')


def randomAsciiBytes (seed : Nat) (len : Nat) : ByteArray × Nat := Id.run do
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


def randomTokenBytes (seed : Nat) (len : Nat) : ByteArray × Nat := Id.run do
  let mut s := seed
  let mut out := ByteArray.empty

  for _ in [0:len] do
    let (r, s') := randBelow s 36
    s := s'

    let code :=
      if r < 26 then
        97 + r
      else
        48 + (r - 26)

    out := out.push (UInt8.ofNat code)

  (out, s)


def randomSplit (seed : Nat) (data : ByteArray) (maxPart : Nat := 17) : Array ByteArray × Nat := Id.run do
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


def randomChunkedPayload (seed : Nat) (body : ByteArray) : ByteArray × Nat := Id.run do
  let mut s := seed
  let mut out := ByteArray.empty
  let mut i := 0

  while i < body.size do
    let remaining := body.size - i
    let maxChunk := Nat.min 9 remaining
    let (chunkLen, s') := randIn s 1 maxChunk
    s := s'

    out := out ++ s!"{chunkLen}\x0d\n".toUTF8
    out := out ++ body.extract i (i + chunkLen)
    out := out ++ "\x0d\n".toUTF8
    i := i + chunkLen

  out := out ++ "0\x0d\n\x0d\n".toUTF8
  (out, s)


def mkContentLengthHead (path : String) (bodySize : Nat) : ByteArray :=
  s!"POST {path} HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: {bodySize}\x0d\nConnection: close\x0d\n\x0d\n".toUTF8


def mkChunkedHead (path : String) : ByteArray :=
  s!"POST {path} HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n".toUTF8


def randomChunkExtensionList (seed : Nat) (count : Nat) : String × Nat := Id.run do
  let mut s := seed
  let mut ext := ""

  for _ in [0:count] do
    let (nameLen, s1) := randIn s 1 3
    s := s1
    let (valueLen, s2) := randIn s 1 3
    s := s2

    let (nameBytes, s3) := randomTokenBytes s nameLen
    s := s3
    let (valueBytes, s4) := randomTokenBytes s valueLen
    s := s4

    let name := String.fromUTF8! nameBytes
    let value := String.fromUTF8! valueBytes
    ext := ext ++ s!";{name}={value}"

  (ext, s)


def randomTrailerLines (seed : Nat) (count : Nat) : String × Nat := Id.run do
  let mut s := seed
  let mut lines := ""

  for i in [0:count] do
    let (nameLen, s1) := randIn s 1 4
    s := s1
    let (valueLen, s2) := randIn s 1 6
    s := s2

    let (nameBytes, s3) := randomTokenBytes s nameLen
    s := s3
    let (valueBytes, s4) := randomTokenBytes s valueLen
    s := s4

    let name := String.fromUTF8! nameBytes
    let value := String.fromUTF8! valueBytes
    lines := lines ++ s!"X{i}-{name}: {value}\x0d\n"

  (lines, s)


def echoBodyHandler : TestHandler := fun req => do
  let body : String ← req.body.readAll
  Response.ok |>.text body


def runPipelinedReadAll
    (raw : ByteArray)
    (config : Config := defaultConfig) : IO (ByteArray × Array String) := Async.block do
  let (client, server) ← Mock.new
  let seenRef ← IO.mkRef (#[] : Array String)

  let handler : TestHandler := fun req => do
    let uri := toString req.head.uri
    seenRef.modify (·.push uri)
    let _body : String ← req.body.readAll
    Response.ok |>.text uri

  client.send raw
  client.getSendChan.close

  Std.Http.Server.serveConnection server handler config
    |>.run

  let response ← client.recv?
  let seen ← seenRef.get
  pure (response.getD .empty, seen)


def fuzzContentLengthEcho (iterations : Nat) (seed0 : Nat) : IO Unit := do
  let mut seed := seed0

  for i in [0:iterations] do
    let caseSeed := seed

    let (len, seed1) := randIn seed 0 128
    seed := seed1

    let (body, seed2) := randomAsciiBytes seed len
    seed := seed2

    let head := mkContentLengthHead s!"/fuzz-cl-{i}" body.size
    let (bodyParts, seed3) := randomSplit seed body
    seed := seed3
    let parts := #[head] ++ bodyParts

    let (client, server) ← Mock.new
    let response ← sendFragmentedAndClose client server parts echoBodyHandler

    let expectedBody := String.fromUTF8! body
    assertStatusPrefix s!"fuzzContentLengthEcho case={i} seed={caseSeed}" response "HTTP/1.1 200"

    let gotBody := responseBody response
    if gotBody != expectedBody then
      throw <| IO.userError s!"fuzzContentLengthEcho case={i} seed={caseSeed} failed:\nExpected body {expectedBody.quote}\nGot body {gotBody.quote}\nFull response:\n{(responseText response).quote}"


def fuzzContentLengthLeadingZerosAccepted (iterations : Nat) (seed0 : Nat) : IO Unit := do
  let mut seed := seed0

  for i in [0:iterations] do
    let caseSeed := seed

    let (len, seed1) := randIn seed 1 96
    seed := seed1

    let (leadingZeros, seed2) := randIn seed 1 5
    seed := seed2

    let (body, seed3) := randomAsciiBytes seed len
    seed := seed3

    let clToken := String.ofList (List.replicate leadingZeros '0') ++ toString len
    let raw :=
      s!"POST /cl-leading-zeros-{i} HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: {clToken}\x0d\nConnection: close\x0d\n\x0d\n".toUTF8 ++ body

    let (client, server) ← Mock.new
    let response ← sendRaw client server raw echoBodyHandler

    let expectedBody := String.fromUTF8! body
    assertStatusPrefix s!"fuzzContentLengthLeadingZerosAccepted case={i} seed={caseSeed} len={len} zeros={leadingZeros}" response "HTTP/1.1 200"

    let gotBody := responseBody response
    if gotBody != expectedBody then
      throw <| IO.userError s!"fuzzContentLengthLeadingZerosAccepted case={i} seed={caseSeed} failed:\nExpected body {expectedBody.quote}\nGot body {gotBody.quote}\nFull response:\n{(responseText response).quote}"


def fuzzChunkedEcho (iterations : Nat) (seed0 : Nat) : IO Unit := do
  let mut seed := seed0

  for i in [0:iterations] do
    let caseSeed := seed

    let (len, seed1) := randIn seed 0 128
    seed := seed1

    let (body, seed2) := randomAsciiBytes seed len
    seed := seed2

    let (chunkedBody, seed3) := randomChunkedPayload seed body
    seed := seed3

    let head := mkChunkedHead s!"/fuzz-chunked-{i}"
    let raw := head ++ chunkedBody

    let (client, server) ← Mock.new
    let response ← sendRaw client server raw echoBodyHandler

    let expectedBody := String.fromUTF8! body
    assertStatusPrefix s!"fuzzChunkedEcho case={i} seed={caseSeed}" response "HTTP/1.1 200"

    let gotBody := responseBody response
    if gotBody != expectedBody then
      throw <| IO.userError s!"fuzzChunkedEcho case={i} seed={caseSeed} failed:\nExpected body {expectedBody.quote}\nGot body {gotBody.quote}\nFull response:\n{(responseText response).quote}"


def fuzzMixedTransferEncodingAndContentLengthRejected (iterations : Nat) (seed0 : Nat) : IO Unit := do
  let mut seed := seed0

  for i in [0:iterations] do
    let caseSeed := seed

    let (len, seed1) := randIn seed 0 96
    seed := seed1

    let (body, seed2) := randomAsciiBytes seed len
    seed := seed2

    let (chunkedBody, seed3) := randomChunkedPayload seed body
    seed := seed3

    let (declaredCl, seed4) := randIn seed 0 128
    seed := seed4

    let raw :=
      s!"POST /te-cl-{i} HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nContent-Length: {declaredCl}\x0d\nConnection: close\x0d\n\x0d\n".toUTF8 ++ chunkedBody

    let (client, server) ← Mock.new
    let response ← sendRaw client server raw echoBodyHandler
    assertExact s!"fuzzMixedTransferEncodingAndContentLengthRejected case={i} seed={caseSeed} declaredCl={declaredCl}" response bad400


def fuzzInvalidChunkSizeRejected (iterations : Nat) (seed0 : Nat) : IO Unit := do
  let badTokens : Array String := #["g", "G", "z", "Z", "@", "!", "x"]
  let mut seed := seed0

  for i in [0:iterations] do
    let caseSeed := seed

    let (idx, seed1) := randBelow seed badTokens.size
    seed := seed1

    let token := badTokens[idx]!
    let raw :=
      s!"POST /bad-size-{i} HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n{token}\x0d\nabc\x0d\n0\x0d\n\x0d\n".toUTF8

    let (client, server) ← Mock.new
    let response ← sendRaw client server raw echoBodyHandler

    assertExact s!"fuzzInvalidChunkSizeRejected case={i} seed={caseSeed} token={token}" response bad400


def fuzzDuplicateContentLengthRejected (iterations : Nat) (seed0 : Nat) : IO Unit := do
  let mut seed := seed0

  for i in [0:iterations] do
    let caseSeed := seed

    let (cl1, seed1) := randIn seed 0 64
    seed := seed1

    let (same, seed2) := randBelow seed 2
    seed := seed2

    let (delta, seed3) := randIn seed 1 10
    seed := seed3

    let cl2 := if same == 0 then cl1 else cl1 + delta
    let (body, seed4) := randomAsciiBytes seed cl1
    seed := seed4

    let raw :=
      s!"POST /dup-cl-{i} HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: {cl1}\x0d\nContent-Length: {cl2}\x0d\nConnection: close\x0d\n\x0d\n".toUTF8 ++ body

    let (client, server) ← Mock.new
    let response ← sendRaw client server raw echoBodyHandler

    assertExact s!"fuzzDuplicateContentLengthRejected case={i} seed={caseSeed} cl1={cl1} cl2={cl2}" response bad400


def fuzzChunkExtensionLimits (iterations : Nat) (seed0 : Nat) : IO Unit := do
  let config : Config := {
    lingeringTimeout := 1000
    generateDate := false
    maxChunkExtNameLength := 4
    maxChunkExtValueLength := 4
  }

  let mut seed := seed0

  for i in [0:iterations] do
    let caseSeed := seed

    let (nameLen, seed1) := randIn seed 1 8
    seed := seed1

    let (valueLen, seed2) := randIn seed 1 8
    seed := seed2

    let (nameBytes, seed3) := randomTokenBytes seed nameLen
    seed := seed3

    let (valueBytes, seed4) := randomTokenBytes seed valueLen
    seed := seed4

    let name := String.fromUTF8! nameBytes
    let value := String.fromUTF8! valueBytes

    let raw :=
      s!"POST /ext-limit-{i} HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n1;{name}={value}\x0d\nx\x0d\n0\x0d\n\x0d\n".toUTF8

    let expectOk := nameLen ≤ 4 ∧ valueLen ≤ 4

    let (client, server) ← Mock.new
    let response ← sendRaw client server raw echoBodyHandler (config := config)

    if expectOk then
      assertStatusPrefix s!"fuzzChunkExtensionLimits case={i} seed={caseSeed} nameLen={nameLen} valueLen={valueLen}" response "HTTP/1.1 200"
    else
      assertExact s!"fuzzChunkExtensionLimits case={i} seed={caseSeed} nameLen={nameLen} valueLen={valueLen}" response bad400


def fuzzChunkExtensionCountLimit (iterations : Nat) (seed0 : Nat) : IO Unit := do
  let config : Config := {
    lingeringTimeout := 1000
    generateDate := false
    maxChunkExtensions := 2
  }

  let mut seed := seed0

  for i in [0:iterations] do
    let caseSeed := seed

    let (extCount, seed1) := randIn seed 0 5
    seed := seed1

    let (extList, seed2) := randomChunkExtensionList seed extCount
    seed := seed2

    let raw :=
      s!"POST /ext-count-{i} HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n1{extList}\x0d\nx\x0d\n0\x0d\n\x0d\n".toUTF8

    let (client, server) ← Mock.new
    let response ← sendRaw client server raw echoBodyHandler (config := config)

    if extCount ≤ 2 then
      assertStatusPrefix s!"fuzzChunkExtensionCountLimit case={i} seed={caseSeed} extCount={extCount}" response "HTTP/1.1 200"
    else
      assertExact s!"fuzzChunkExtensionCountLimit case={i} seed={caseSeed} extCount={extCount}" response bad400


def fuzzTrailerHeaderCountLimit (iterations : Nat) (seed0 : Nat) : IO Unit := do
  let config : Config := {
    lingeringTimeout := 1000
    generateDate := false
    maxTrailerHeaders := 2
  }

  let mut seed := seed0

  for i in [0:iterations] do
    let caseSeed := seed

    let (trailerCount, seed1) := randIn seed 0 5
    seed := seed1

    let (trailers, seed2) := randomTrailerLines seed trailerCount
    seed := seed2

    let raw :=
      s!"POST /trailers-{i} HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n1\x0d\na\x0d\n0\x0d\n{trailers}\x0d\n".toUTF8

    let (client, server) ← Mock.new
    let response ← sendRaw client server raw echoBodyHandler (config := config)

    if trailerCount ≤ 2 then
      assertStatusPrefix s!"fuzzTrailerHeaderCountLimit case={i} seed={caseSeed} trailerCount={trailerCount}" response "HTTP/1.1 200"
    else
      assertExact s!"fuzzTrailerHeaderCountLimit case={i} seed={caseSeed} trailerCount={trailerCount}" response bad400


def fuzzIncompleteFirstBodyBlocksPipeline (iterations : Nat) (seed0 : Nat) : IO Unit := do
  let mut seed := seed0

  for i in [0:iterations] do
    let caseSeed := seed

    let (declaredLen, seed1) := randIn seed 1 32
    seed := seed1

    let (actualLen, seed2) := randIn seed 0 (declaredLen - 1)
    seed := seed2

    let (body, seed3) := randomAsciiBytes seed actualLen
    seed := seed3

    let uri1 := s!"/first-incomplete-{i}"
    let req1 :=
      s!"POST {uri1} HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: {declaredLen}\x0d\n\x0d\n".toUTF8 ++ body
    let req2 := "GET /second HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8

    let (response, seen) ← runPipelinedReadAll (req1 ++ req2)

    let text := responseText response

    unless text.contains uri1 do
      throw <| IO.userError s!"fuzzIncompleteFirstBodyBlocksPipeline case={i} seed={caseSeed} failed:\nMissing first URI {uri1.quote}\n{text.quote}"

    if text.contains "/second" then
      throw <| IO.userError s!"fuzzIncompleteFirstBodyBlocksPipeline case={i} seed={caseSeed} failed:\nUnexpected second response\n{text.quote}"

    if seen.size != 1 ∨ seen[0]! != uri1 then
      throw <| IO.userError s!"fuzzIncompleteFirstBodyBlocksPipeline case={i} seed={caseSeed} failed:\nExpected seen=[{uri1.quote}] got {seen}"


def fuzzCompleteFirstBodyAllowsPipeline (iterations : Nat) (seed0 : Nat) : IO Unit := do
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


-- Property: Content-Length framing is stable across random payloads and random transport splits.
#eval runWithTimeout "fuzz_content_length_echo" 20000 do
  fuzzContentLengthEcho 40 0x00C0FFEE

-- Property: Content-Length with randomized leading zeros is accepted and decoded to exact body length.
#eval runWithTimeout "fuzz_content_length_leading_zeros_accepted" 20000 do
  fuzzContentLengthLeadingZerosAccepted 30 0x00CAB005

-- Property: Chunked framing reconstructs exact bodies under random chunking and transport splits.
#eval runWithTimeout "fuzz_chunked_echo" 20000 do
  fuzzChunkedEcho 40 0x00123456

-- Property: Mixing Transfer-Encoding with Content-Length is always rejected.
#eval runWithTimeout "fuzz_te_cl_mixed_rejected" 20000 do
  fuzzMixedTransferEncodingAndContentLengthRejected 30 0x0010CE11

-- Property: Invalid chunk-size tokens are rejected deterministically with 400.
#eval runWithTimeout "fuzz_invalid_chunk_size_rejected" 20000 do
  fuzzInvalidChunkSizeRejected 30 0x00BAD001

-- Property: Duplicate Content-Length headers are always rejected (same or different values).
#eval runWithTimeout "fuzz_duplicate_content_length_rejected" 20000 do
  fuzzDuplicateContentLengthRejected 30 0x00D0C1A7

-- Property: Chunk extension name/value limits are enforced under randomized lengths.
#eval runWithTimeout "fuzz_chunk_extension_limits" 20000 do
  fuzzChunkExtensionLimits 40 0x00A11CE5

-- Property: Chunk extension count limit is enforced under randomized extension lists.
#eval runWithTimeout "fuzz_chunk_extension_count_limit" 20000 do
  fuzzChunkExtensionCountLimit 35 0x00E77E11

-- Property: Trailer header count limit is enforced under randomized trailer sections.
#eval runWithTimeout "fuzz_trailer_header_count_limit" 20000 do
  fuzzTrailerHeaderCountLimit 35 0x00A71A12

-- Property: Incomplete first request body blocks pipelined follow-up parsing.
#eval runWithTimeout "fuzz_incomplete_first_body_blocks_pipeline" 20000 do
  fuzzIncompleteFirstBodyBlocksPipeline 30 0x00331337

-- Property: Complete first request body allows pipelined follow-up parsing.
#eval runWithTimeout "fuzz_complete_first_body_allows_pipeline" 20000 do
  fuzzCompleteFirstBodyAllowsPipeline 30 0x00777777
