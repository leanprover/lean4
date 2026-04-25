import Std.Http
import Std.Async

open Std.Async
open Std Http Internal Test

/-!
# Limit-enforcement fuzzing for the HTTP/1.1 server.

Tests that every configurable limit in `H1.Config` and `Server.Config` is
correctly enforced under randomized inputs. Inspired by hyper's fuzzing of
size and count limits.
-/

def closeChannelIdempotent {α : Type} (ch : Std.CloseableChannel α) : IO Unit := do
  match ← EIO.toBaseIO ch.close with
  | .ok _ => pure ()
  | .error .alreadyClosed => pure ()
  | .error err => throw <| IO.userError (toString err)

def sendRaw
    (client : Mock.Client) (server : Mock.Server) (raw : ByteArray)
    (handler : TestHandler) (config : Config) : IO ByteArray := Async.block do
  client.send raw
  Std.Http.Server.serveConnection server handler config |>.run
  let res ← client.recv?
  pure (res.getD .empty)

def sendRawAndClose
    (client : Mock.Client) (server : Mock.Server) (raw : ByteArray)
    (handler : TestHandler) (config : Config) : IO ByteArray := Async.block do
  client.send raw
  closeChannelIdempotent client.getSendChan
  Std.Http.Server.serveConnection server handler config |>.run
  let res ← client.recv?
  pure (res.getD .empty)

def runWithTimeout {α : Type} (name : String) (timeoutMs : Nat := 20000) (action : IO α) : IO α := do
  let task ← IO.asTask action
  let ticks := (timeoutMs + 9) / 10
  let rec loop (remaining : Nat) : IO α := do
    if (← IO.getTaskState task) == .finished then
      match (← IO.wait task) with
      | .ok x => pure x
      | .error err => throw err
    else
      match remaining with
      | 0 => IO.cancel task; throw <| IO.userError s!"Test '{name}' timed out"
      | n + 1 => IO.sleep 10; loop n
  loop ticks

-- PRNG
def nextSeed (seed : Nat) : Nat := (1664525 * seed + 1013904223) % 4294967296
def randBelow (seed : Nat) (n : Nat) : Nat × Nat :=
  let s := nextSeed seed
  (if n == 0 then 0 else s % n, s)
def randIn (seed : Nat) (lo hi : Nat) : Nat × Nat :=
  if hi < lo then (lo, seed) else
  let (r, s) := randBelow seed (hi - lo + 1)
  (lo + r, s)

def randomTokenBytes (seed : Nat) (len : Nat) : ByteArray × Nat := Id.run do
  let mut s := seed; let mut out := ByteArray.empty
  for _ in [0:len] do
    let (r, s') := randBelow s 36; s := s'
    let code := if r < 26 then 97 + r else 48 + (r - 26)
    out := out.push (UInt8.ofNat code)
  (out, s)

def randomAsciiBytes (seed : Nat) (len : Nat) : ByteArray × Nat := Id.run do
  let mut s := seed; let mut out := ByteArray.empty
  for _ in [0:len] do
    let (r, s') := randBelow s 26; s := s'
    out := out.push (UInt8.ofNat (97 + r))
  (out, s)

private def toHexAux : Nat → Nat → String → String
  | 0, _, acc => acc
  | fuel + 1, n, acc =>
    if n == 0 then acc
    else
      let d := n % 16
      let c : Char := if d < 10 then Char.ofNat (48 + d) else Char.ofNat (87 + d)
      toHexAux fuel (n / 16) (String.ofList [c] ++ acc)

def natToHex (n : Nat) : String :=
  if n == 0 then "0" else toHexAux 16 n ""

def assertStatusPrefix (name : String) (response : ByteArray) (pfx : String) : IO Unit := do
  let text := String.fromUTF8! response
  unless text.startsWith pfx do
    throw <| IO.userError s!"Test '{name}' failed:\nExpected {pfx.quote}\nGot:\n{text.quote}"

def countOccurrences (s needle : String) : Nat :=
  if needle.isEmpty then 0 else (s.splitOn needle).length - 1

def bad400 : String :=
  "HTTP/1.1 400 Bad Request\x0d\nServer: LeanHTTP/1.1\x0d\nConnection: close\x0d\nContent-Length: 0\x0d\n\x0d\n"

def echoBodyHandler : TestHandler := fun req => do
  let body : String ← req.body.readAll
  Response.ok |>.text body

-- ============================================================================
-- maxBodySize — Content-Length framing
-- ============================================================================

-- Property: Content-Length body exactly at or below maxBodySize → 200.
--           Content-Length body above maxBodySize → 413 (no body bytes needed).
def fuzzBodySizeLimitContentLength (iterations : Nat) (seed0 : Nat) : IO Unit := do
  let limit : Nat := 64
  let config : Config := { lingeringTimeout := 1000, generateDate := false, maxBodySize := limit }
  let mut seed := seed0
  for i in [0:iterations] do
    let caseSeed := seed
    let (bodySize, s1) := randIn seed 0 (limit + 20); seed := s1
    let (bodyBytes, s2) := randomAsciiBytes seed bodySize; seed := s2
    let raw :=
      s!"POST /bl-cl-{i} HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: {bodySize}\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
      ++ bodyBytes
    let (client, server) ← Mock.new
    let response ← sendRaw client server raw (fun req => do
      let _body : String ← req.body.readAll; Response.ok |>.text "ok") config
    if bodySize ≤ limit then
      assertStatusPrefix s!"fuzzBodySizeLimitCL iter={i} seed={caseSeed} size={bodySize}" response "HTTP/1.1 200"
    else
      assertStatusPrefix s!"fuzzBodySizeLimitCL iter={i} seed={caseSeed} size={bodySize}" response "HTTP/1.1 413"

-- ============================================================================
-- maxBodySize — chunked framing
-- ============================================================================

-- Property: chunked bodies with total bytes at or below maxBodySize → 200.
--           Chunked bodies exceeding maxBodySize → 413.
def fuzzBodySizeLimitChunked (iterations : Nat) (seed0 : Nat) : IO Unit := do
  let limit : Nat := 64
  let config : Config := { lingeringTimeout := 1000, generateDate := false, maxBodySize := limit }
  let mut seed := seed0
  for i in [0:iterations] do
    let caseSeed := seed
    -- Total body size across 1-4 chunks
    let (totalSize, s1) := randIn seed 0 (limit + 16); seed := s1
    let (numChunks, s2) := randIn seed 1 4; seed := s2

    -- Build chunks that sum to totalSize
    let chunkSize := (totalSize + numChunks - 1) / numChunks
    let mut chunkedBody := ByteArray.empty
    let mut remaining := totalSize
    for _ in [0:numChunks] do
      if remaining == 0 then break
      let thisChunk := Nat.min chunkSize remaining
      let (chunkBytes, s3) := randomAsciiBytes seed thisChunk; seed := s3
      chunkedBody := chunkedBody ++ s!"{natToHex thisChunk}\x0d\n".toUTF8 ++ chunkBytes ++ "\x0d\n".toUTF8
      remaining := remaining - thisChunk
    chunkedBody := chunkedBody ++ "0\x0d\n\x0d\n".toUTF8

    let raw :=
      s!"POST /bl-ch-{i} HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
      ++ chunkedBody
    let (client, server) ← Mock.new
    let response ← sendRaw client server raw (fun req => do
      let _body : String ← req.body.readAll; Response.ok |>.text "ok") config
    if totalSize ≤ limit then
      assertStatusPrefix s!"fuzzBodySizeLimitChunked iter={i} seed={caseSeed} total={totalSize}" response "HTTP/1.1 200"
    else
      assertStatusPrefix s!"fuzzBodySizeLimitChunked iter={i} seed={caseSeed} total={totalSize}" response "HTTP/1.1 413"

-- ============================================================================
-- maxHeaders — header count limit
-- ============================================================================

-- Property: header count at or below maxHeaders → 200.
--           header count above maxHeaders → 400.
def fuzzHeaderCountLimit (iterations : Nat) (seed0 : Nat) : IO Unit := do
  let limit : Nat := 5
  let config : Config := { lingeringTimeout := 1000, generateDate := false, maxHeaders := limit }
  let mut seed := seed0
  for i in [0:iterations] do
    let caseSeed := seed
    -- Host counts as 1 header, Connection as 1, so extra headers = headerCount - 2
    let (headerCount, s1) := randIn seed 2 (limit + 4); seed := s1
    let extraCount := headerCount - 2  -- we always add Host + Connection

    let mut extraHeaders := ""
    let mut s := s1
    for j in [0:extraCount] do
      let (nameLen, s2) := randIn s 1 8; s := s2
      let (nameBytes, s3) := randomTokenBytes s nameLen; s := s3
      let name := String.fromUTF8! nameBytes
      extraHeaders := extraHeaders ++ s!"X-Extra-{j}-{name}: value\x0d\n"
    seed := s

    let raw :=
      s!"GET /hc-{i} HTTP/1.1\x0d\nHost: example.com\x0d\n{extraHeaders}Connection: close\x0d\n\x0d\n".toUTF8
    let (client, server) ← Mock.new
    let response ← sendRawAndClose client server raw okHandler config
    -- headerCount includes Host and Connection (always present)
    if headerCount ≤ limit then
      assertStatusPrefix s!"fuzzHeaderCount iter={i} seed={caseSeed} count={headerCount}" response "HTTP/1.1 200"
    else
      assertStatusPrefix s!"fuzzHeaderCount iter={i} seed={caseSeed} count={headerCount}" response "HTTP/1.1 431"

-- ============================================================================
-- maxHeaderBytes — total header bytes limit
-- ============================================================================

-- Property: headers whose aggregate bytes (name + ": " + value + "\r\n") are at or
--           below maxHeaderBytes are accepted; above it they are rejected with 400.
def fuzzHeaderTotalBytesLimit (iterations : Nat) (seed0 : Nat) : IO Unit := do
  -- Fixed baseline: "Host: example.com\r\n" + "Connection: close\r\n" = 20 + 20 = 40 bytes.
  -- We'll add a single large X-Payload header to cross the boundary.
  let limit : Nat := 200
  let config : Config := {
    lingeringTimeout := 1000
    generateDate := false
    maxHeaderBytes := limit
    maxHeaderValueLength := limit + 100  -- allow value longer than total limit for testing
  }
  let baseline := ("Host: example.com\x0d\nConnection: close\x0d\n".toUTF8).size
  let mut seed := seed0
  for i in [0:iterations] do
    let caseSeed := seed
    -- Pick a value size that puts total bytes just under or over the limit
    -- Each "X-Payload: " header = name(9) + ": "(2) + value + "\r\n"(2) = value + 13
    let overhead := baseline + 13  -- "X-Payload" (9) + ": " (2) + "\r\n" (2) + baseline
    -- We want value sizes that land on both sides of (limit - overhead)
    let boundary := if limit > overhead then limit - overhead else 0
    let (valueSize, s1) := randIn seed 0 (boundary + 20); seed := s1
    let (valueBytes, s2) := randomAsciiBytes seed valueSize; seed := s2
    let value := String.fromUTF8! valueBytes

    let raw :=
      s!"GET /hb-{i} HTTP/1.1\x0d\nHost: example.com\x0d\nX-Payload: {value}\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
    let (client, server) ← Mock.new
    let response ← sendRawAndClose client server raw okHandler config
    -- Total bytes = baseline + "X-Payload: " + value + "\r\n"
    let totalBytes := baseline + 9 + 2 + valueSize + 2
    if totalBytes ≤ limit then
      assertStatusPrefix s!"fuzzHeaderBytes iter={i} seed={caseSeed} total={totalBytes}" response "HTTP/1.1 200"
    else
      assertStatusPrefix s!"fuzzHeaderBytes iter={i} seed={caseSeed} total={totalBytes}" response "HTTP/1.1 431"

-- ============================================================================
-- maxMessages — requests per connection
-- ============================================================================

-- Property: after maxMessages requests on a single connection, the server
--           closes the connection (disables keep-alive). All maxMessages
--           requests receive a valid response.
def fuzzMaxMessagesPerConnection (iterations : Nat) (seed0 : Nat) : IO Unit := do
  let limit : Nat := 3
  let config : Config := {
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

-- ============================================================================
-- maxLeadingEmptyLines — leading CRLF before request-line
-- ============================================================================

-- Property: at most maxLeadingEmptyLines bare CRLFs before the request-line are tolerated.
--           More than that → 400.
def fuzzLeadingEmptyLinesLimit (iterations : Nat) (seed0 : Nat) : IO Unit := do
  let limit : Nat := 4
  let config : Config := { lingeringTimeout := 1000, generateDate := false, maxLeadingEmptyLines := limit }
  let mut seed := seed0
  for i in [0:iterations] do
    let caseSeed := seed
    let (lineCount, s1) := randIn seed 0 (limit + 4); seed := s1
    let leadingCRLF := (List.replicate lineCount "\x0d\n").foldl (· ++ ·) ""
    let raw :=
      (leadingCRLF ++ s!"GET /le-{i} HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n").toUTF8
    let (client, server) ← Mock.new
    let response ← sendRawAndClose client server raw okHandler config
    if lineCount ≤ limit then
      assertStatusPrefix s!"fuzzLeadingEmptyLines iter={i} seed={caseSeed} count={lineCount}" response "HTTP/1.1 200"
    else
      assertStatusPrefix s!"fuzzLeadingEmptyLines iter={i} seed={caseSeed} count={lineCount}" response "HTTP/1.1 400"

-- ============================================================================
-- maxSpaceSequence — OWS (optional whitespace) limit
-- ============================================================================

-- Property: OWS sequences at or below maxSpaceSequence are accepted.
--           OWS sequences exceeding the limit → 400.
def fuzzOWSSequenceLimit (iterations : Nat) (seed0 : Nat) : IO Unit := do
  let limit : Nat := 4
  let config : Config := { lingeringTimeout := 1000, generateDate := false, maxSpaceSequence := limit }
  let mut seed := seed0
  for i in [0:iterations] do
    let caseSeed := seed
    let (spaceCount, s1) := randIn seed 0 (limit + 4); seed := s1
    let spaces := String.ofList (List.replicate spaceCount ' ')
    -- OWS appears between ':' and value in header fields
    let raw :=
      s!"GET /ows-{i} HTTP/1.1\x0d\nHost: example.com\x0d\nX-OWS:{spaces}value\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
    let (client, server) ← Mock.new
    let response ← sendRawAndClose client server raw okHandler config
    if spaceCount ≤ limit then
      assertStatusPrefix s!"fuzzOWSLimit iter={i} seed={caseSeed} spaces={spaceCount}" response "HTTP/1.1 200"
    else
      assertStatusPrefix s!"fuzzOWSLimit iter={i} seed={caseSeed} spaces={spaceCount}" response "HTTP/1.1 400"

-- ============================================================================
-- maxStartLineLength — request-line length limit
-- ============================================================================

-- Property: request lines at or below maxStartLineLength → 200.
--           Request lines above maxStartLineLength → 414 (URI too long) or 400.
def fuzzStartLineLengthLimit (iterations : Nat) (seed0 : Nat) : IO Unit := do
  let limit : Nat := 64
  let config : Config := {
    lingeringTimeout := 1000
    generateDate := false
    maxStartLineLength := limit
    maxUriLength := limit
  }
  let mut seed := seed0
  for i in [0:iterations] do
    let caseSeed := seed
    -- "GET " (4) + path + " HTTP/1.1\r\n" (12) → path can be up to (limit - 16)
    let pathBudget := if limit > 16 then limit - 16 else 1
    let (pathLen, s1) := randIn seed 1 (pathBudget + 10); seed := s1
    let path := "/" ++ String.ofList (List.replicate (pathLen - 1) 'a')
    let raw :=
      s!"GET {path} HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
    let (client, server) ← Mock.new
    let response ← sendRawAndClose client server raw okHandler config
    -- start-line = "GET " + path + " HTTP/1.1\r\n"
    let lineLen := 4 + pathLen + 11
    if lineLen ≤ limit then
      assertStatusPrefix s!"fuzzStartLineLen iter={i} seed={caseSeed} len={lineLen}" response "HTTP/1.1 200"
    else
      -- Either 414 (URI too long) or 400
      let text := String.fromUTF8! response
      unless text.startsWith "HTTP/1.1 414" || text.startsWith "HTTP/1.1 400" do
        throw <| IO.userError
          s!"fuzzStartLineLen iter={i} seed={caseSeed} len={lineLen}: expected 414 or 400, got {text.quote}"

-- ============================================================================
-- maxHeaderNameLength and maxHeaderValueLength
-- ============================================================================

-- Property: header names exceeding maxHeaderNameLength → 400.
def fuzzHeaderNameLengthLimit (iterations : Nat) (seed0 : Nat) : IO Unit := do
  let limit : Nat := 16
  let config : Config := { lingeringTimeout := 1000, generateDate := false, maxHeaderNameLength := limit }
  let mut seed := seed0
  for i in [0:iterations] do
    let caseSeed := seed
    let (nameLen, s1) := randIn seed 1 (limit + 8); seed := s1
    let (nameBytes, s2) := randomTokenBytes seed nameLen; seed := s2
    let name := String.fromUTF8! nameBytes
    let raw :=
      s!"GET /hnl-{i} HTTP/1.1\x0d\nHost: example.com\x0d\n{name}: value\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
    let (client, server) ← Mock.new
    let response ← sendRawAndClose client server raw okHandler config
    if nameLen ≤ limit then
      assertStatusPrefix s!"fuzzHeaderNameLen iter={i} seed={caseSeed} len={nameLen}" response "HTTP/1.1 200"
    else
      assertStatusPrefix s!"fuzzHeaderNameLen iter={i} seed={caseSeed} len={nameLen}" response "HTTP/1.1 400"

-- Property: header values exceeding maxHeaderValueLength → 400.
def fuzzHeaderValueLengthLimit (iterations : Nat) (seed0 : Nat) : IO Unit := do
  let limit : Nat := 32
  let config : Config := {
    lingeringTimeout := 1000
    generateDate := false
    maxHeaderValueLength := limit
    maxHeaderBytes := 65536  -- don't let total bytes limit interfere
  }
  let mut seed := seed0
  for i in [0:iterations] do
    let caseSeed := seed
    let (valueLen, s1) := randIn seed 0 (limit + 8); seed := s1
    let (valueBytes, s2) := randomAsciiBytes seed valueLen; seed := s2
    let value := String.fromUTF8! valueBytes
    let raw :=
      s!"GET /hvl-{i} HTTP/1.1\x0d\nHost: example.com\x0d\nX-Long: {value}\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
    let (client, server) ← Mock.new
    let response ← sendRawAndClose client server raw okHandler config
    if valueLen ≤ limit then
      assertStatusPrefix s!"fuzzHeaderValueLen iter={i} seed={caseSeed} len={valueLen}" response "HTTP/1.1 200"
    else
      assertStatusPrefix s!"fuzzHeaderValueLen iter={i} seed={caseSeed} len={valueLen}" response "HTTP/1.1 400"

-- ============================================================================
-- Run all properties
-- ============================================================================

-- Property: maxBodySize enforced for Content-Length framing.
#eval runWithTimeout "fuzz_body_limit_content_length" 30000 do
  fuzzBodySizeLimitContentLength 50 0x00B0DEC0

-- Property: maxBodySize enforced for chunked framing.
#eval runWithTimeout "fuzz_body_limit_chunked" 30000 do
  fuzzBodySizeLimitChunked 40 0x00C8BE11

-- Property: maxHeaders count limit is enforced.
#eval runWithTimeout "fuzz_header_count_limit" 30000 do
  fuzzHeaderCountLimit 50 0x00AA55AA

-- Property: maxHeaderBytes aggregate limit is enforced.
#eval runWithTimeout "fuzz_header_bytes_limit" 30000 do
  fuzzHeaderTotalBytesLimit 40 0x00FACE77

-- Property: maxMessages per connection closes keep-alive after the configured count.
#eval runWithTimeout "fuzz_max_messages_per_connection" 30000 do
  fuzzMaxMessagesPerConnection 30 0x00123ABC

-- Property: maxLeadingEmptyLines limit is enforced.
#eval runWithTimeout "fuzz_leading_empty_lines_limit" 30000 do
  fuzzLeadingEmptyLinesLimit 50 0x00EEF00D

-- Property: maxSpaceSequence (OWS) limit is enforced.
#eval runWithTimeout "fuzz_ows_sequence_limit" 30000 do
  fuzzOWSSequenceLimit 50 0x00ABE5AB

-- Property: maxStartLineLength / maxUriLength is enforced, returning 414 or 400.
#eval runWithTimeout "fuzz_start_line_length_limit" 30000 do
  fuzzStartLineLengthLimit 50 0x00C0FFEE

-- Property: maxHeaderNameLength is enforced.
#eval runWithTimeout "fuzz_header_name_length_limit" 30000 do
  fuzzHeaderNameLengthLimit 50 0x00DEAD01

-- Property: maxHeaderValueLength is enforced.
#eval runWithTimeout "fuzz_header_value_length_limit" 30000 do
  fuzzHeaderValueLengthLimit 50 0x00BEEF02
