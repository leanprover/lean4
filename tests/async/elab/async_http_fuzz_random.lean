import Std.Http
import Std.Async

open Std.Async
open Std Http Internal Test

/-!
# Random-byte fuzzing for the HTTP/1.1 parser.

Inspired by hyper's `fuzz_h1_req` libFuzzer target. The core property: any byte
sequence fed to the server must be handled without panicking, hanging, or
producing a malformed response. The server must either:
- Send no bytes (connection closed before a complete request arrives), or
- Send a response that starts with "HTTP/1.1 ".
-/

def closeChannelIdempotent {α : Type} (ch : Std.CloseableChannel α) : IO Unit := do
  match ← EIO.toBaseIO ch.close with
  | .ok _ => pure ()
  | .error .alreadyClosed => pure ()
  | .error err => throw <| IO.userError (toString err)

def sendRawAndClose
    (client : Mock.Client) (server : Mock.Server) (raw : ByteArray)
    (handler : TestHandler) (config : Config := defaultConfig) : IO ByteArray := Async.block do
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

-- All 256 byte values
def randomFullBytes (seed : Nat) (len : Nat) : ByteArray × Nat := Id.run do
  let mut s := seed; let mut out := ByteArray.empty
  for _ in [0:len] do
    let (r, s') := randBelow s 256; s := s'
    out := out.push (UInt8.ofNat r)
  (out, s)

-- Server-generated responses are always valid ASCII. Verify the response is
-- either empty or starts with the HTTP/1.1 status-line prefix.
def assertValidHttpOrEmpty (name : String) (response : ByteArray) : IO Unit := do
  if response.size == 0 then pure ()
  else
    let isValidPrefix (pfx : String) :=
      let b := pfx.toUTF8
      response.size >= b.size && response.extract 0 b.size == b
    if isValidPrefix "HTTP/1.1 " || isValidPrefix "HTTP/1.0 " then pure ()
    else
      let display := match String.fromUTF8? (response.extract 0 (Nat.min 200 response.size)) with
        | some s => s.quote | none => "(non-UTF-8 bytes)"
      throw <| IO.userError
        s!"Test '{name}' failed:\nResponse is neither empty nor a valid HTTP response:\n{display}"

-- Property: any fully-random byte sequence never causes a panic or malformed response.
-- Direct analogue of hyper's fuzz_h1_req libFuzzer target.
def fuzzRandomBytesNoPanic (iterations : Nat) (seed0 : Nat) : IO Unit := do
  let mut seed := seed0
  for i in [0:iterations] do
    let caseSeed := seed
    let (len, s1) := randIn seed 0 96; seed := s1
    let (bytes, s2) := randomFullBytes seed len; seed := s2
    let (client, server) ← Mock.new
    let response ← sendRawAndClose client server bytes okHandler
    assertValidHttpOrEmpty s!"fuzzRandomBytesNoPanic iter={i} seed={caseSeed} len={len}" response

-- Property: flipping a single bit in any valid request must not cause a panic.
def fuzzBitFlipOnValidRequests (iterations : Nat) (seed0 : Nat) : IO Unit := do
  let corpus : Array ByteArray := #[
    "GET / HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8,
    "POST /submit HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 5\x0d\nConnection: close\x0d\n\x0d\nhello".toUTF8,
    "POST /chunked HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8,
    "OPTIONS * HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8,
    "CONNECT example.com:443 HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8,
    "DELETE /resource HTTP/1.1\x0d\nHost: api.example.com\x0d\nAuthorization: Bearer token123\x0d\nConnection: close\x0d\n\x0d\n".toUTF8,
  ]
  let mut seed := seed0
  for i in [0:iterations] do
    let caseSeed := seed
    let (idx, s1) := randBelow seed corpus.size; seed := s1
    let req := corpus[idx]!
    let (pos, s2) := randBelow seed req.size; seed := s2
    let (bit, s3) := randBelow seed 8; seed := s3
    let orig := req[pos]!
    let mask : UInt8 := (1 : UInt8) <<< bit.toUInt8
    let flipped := orig ^^^ mask
    let mutated := (req.extract 0 pos).push flipped ++ req.extract (pos + 1) req.size
    let (client, server) ← Mock.new
    let response ← sendRawAndClose client server mutated okHandler
    assertValidHttpOrEmpty
      s!"fuzzBitFlip iter={i} seed={caseSeed} reqIdx={idx} pos={pos} bit={bit}" response

-- Property: truncating a valid request at any byte boundary must not cause a panic.
def fuzzTruncatedRequests (iterations : Nat) (seed0 : Nat) : IO Unit := do
  let corpus : Array ByteArray := #[
    "GET / HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8,
    "POST /data HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 4\x0d\nConnection: close\x0d\n\x0d\ndata".toUTF8,
    "POST /chunked HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n4\x0d\ndata\x0d\n0\x0d\n\x0d\n".toUTF8,
    "HEAD /resource HTTP/1.1\x0d\nHost: example.com\x0d\nAccept: application/json\x0d\nConnection: close\x0d\n\x0d\n".toUTF8,
  ]
  let mut seed := seed0
  for i in [0:iterations] do
    let caseSeed := seed
    let (idx, s1) := randBelow seed corpus.size; seed := s1
    let req := corpus[idx]!
    let (truncLen, s2) := randBelow seed req.size; seed := s2
    let truncated := req.extract 0 truncLen
    let (client, server) ← Mock.new
    let response ← sendRawAndClose client server truncated okHandler
    assertValidHttpOrEmpty
      s!"fuzzTruncated iter={i} seed={caseSeed} reqIdx={idx} truncLen={truncLen}" response

-- Property: a valid HTTP method prefix followed by garbage must not cause a panic.
def fuzzMethodPrefixWithGarbage (iterations : Nat) (seed0 : Nat) : IO Unit := do
  let methods : Array ByteArray := #[
    "GET ".toUTF8, "POST ".toUTF8, "PUT ".toUTF8, "DELETE ".toUTF8,
    "HEAD ".toUTF8, "OPTIONS ".toUTF8, "PATCH ".toUTF8, "CONNECT ".toUTF8,
    "HTTP/1.1 ".toUTF8,
    ByteArray.empty,
  ]
  let mut seed := seed0
  for i in [0:iterations] do
    let caseSeed := seed
    let (mIdx, s1) := randBelow seed methods.size; seed := s1
    let pfx := methods[mIdx]!
    let (gLen, s2) := randIn seed 0 64; seed := s2
    let (garbage, s3) := randomFullBytes seed gLen; seed := s3
    let request := pfx ++ garbage
    let (client, server) ← Mock.new
    let response ← sendRawAndClose client server request okHandler
    assertValidHttpOrEmpty
      s!"fuzzMethodPrefix iter={i} seed={caseSeed} mIdx={mIdx} gLen={gLen}" response

-- Property: high-byte (0x80–0xFF, non-ASCII) sequences must not cause a panic.
def fuzzHighByteValues (iterations : Nat) (seed0 : Nat) : IO Unit := do
  let mut seed := seed0
  for i in [0:iterations] do
    let caseSeed := seed
    let (len, s1) := randIn seed 0 48; seed := s1
    let mut out := ByteArray.empty
    let mut s := s1
    for _ in [0:len] do
      let (r, s') := randBelow s 128; s := s'
      out := out.push (UInt8.ofNat (r + 128))
    seed := s
    let (client, server) ← Mock.new
    let response ← sendRawAndClose client server out okHandler
    assertValidHttpOrEmpty s!"fuzzHighBytes iter={i} seed={caseSeed} len={len}" response

-- Property: garbage appended after a complete request must not cause a panic.
def fuzzGarbageAfterCompleteRequest (iterations : Nat) (seed0 : Nat) : IO Unit := do
  let validReq :=
    "GET /check HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let mut seed := seed0
  for i in [0:iterations] do
    let caseSeed := seed
    let (gLen, s1) := randIn seed 0 32; seed := s1
    let (garbage, s2) := randomFullBytes seed gLen; seed := s2
    let request := validReq ++ garbage
    let (client, server) ← Mock.new
    let response ← sendRawAndClose client server request okHandler
    assertValidHttpOrEmpty
      s!"fuzzGarbageAfter iter={i} seed={caseSeed} gLen={gLen}" response

-- Property: every single-byte input is handled safely (all 256 values).
def fuzzSingleByteInputs : IO Unit := do
  for b in List.range 256 do
    let bytes := ByteArray.mk #[b.toUInt8]
    let (client, server) ← Mock.new
    let response ← sendRawAndClose client server bytes okHandler
    assertValidHttpOrEmpty s!"fuzzSingleByte byte={b}" response

-- Property: known attack patterns and real-world malformed inputs are handled safely.
-- This is the Lean analogue of hyper's denial-of-service and smuggling corpus.
def fuzzKnownMaliciousPatterns : IO Unit := do
  let patterns : Array ByteArray := #[
    -- TLS 1.2 client hello prefix
    ByteArray.mk #[0x16, 0x03, 0x01, 0x00, 0xa5, 0x01, 0x00, 0x00],
    -- TLS 1.3 client hello prefix
    ByteArray.mk #[0x16, 0x03, 0x03, 0x00, 0x7c, 0x01, 0x00, 0x00],
    -- HTTP/2 connection preface
    "PRI * HTTP/2.0\x0d\n\x0d\nSM\x0d\n\x0d\n".toUTF8,
    -- Bare LF line endings
    "GET / HTTP/1.1\nHost: example.com\n\n".toUTF8,
    -- CR-only line endings
    "GET / HTTP/1.1\x0dHost: example.com\x0d\x0d".toUTF8,
    -- Null bytes everywhere
    ByteArray.mk #[0x00, 0x00, 0x00, 0x00],
    -- CRLF injection attempt in request-line
    "GET /path%0d%0aInjected: header HTTP/1.1\x0d\nHost: example.com\x0d\n\x0d\n".toUTF8,
    -- Unicode in path (raw multibyte UTF-8)
    "GET /caf\xc3\xa9 HTTP/1.1\x0d\nHost: example.com\x0d\n\x0d\n".toUTF8,
    -- HTTP response sent as a request (should fail, not panic)
    "HTTP/1.1 200 OK\x0d\nContent-Length: 2\x0d\n\x0d\nok".toUTF8,
    -- Request smuggling: CL.TE
    "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 6\x0d\nTransfer-Encoding: chunked\x0d\n\x0d\n0\x0d\n\x0d\nX".toUTF8,
    -- Request smuggling: TE.CL
    "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nContent-Length: 3\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8,
    -- Duplicate chunked coding
    "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked, chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8,
    -- TE with tab (whitespace obfuscation)
    "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding:\x09chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8,
    -- TE with null byte injection
    "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunk\x00ed\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8,
    -- Extremely long method token
    (String.ofList (List.replicate 8192 'A') ++ " / HTTP/1.1\x0d\nHost: h\x0d\n\x0d\n").toUTF8,
    -- SSRF-like absolute-form URI targeting internal host
    "GET http://169.254.169.254/latest/meta-data/ HTTP/1.1\x0d\nHost: example.com\x0d\n\x0d\n".toUTF8,
    -- Chunk size with non-hex chars
    "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\nGG\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8,
    -- Chunk size overflow attempt (16+ hex digits)
    "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\nffffffffffffffff1\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8,
    -- Header with embedded CRLF in value
    "GET / HTTP/1.1\x0d\nHost: example.com\x0d\nX-Inject: foo\x0d\nEvil: injected\x0d\nConnection: close\x0d\n\x0d\n".toUTF8,
    -- Multiple Host headers (smuggling attempt)
    "GET / HTTP/1.1\x0d\nHost: example.com\x0d\nHost: evil.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8,
    -- Absolute-form URI with bad host overrides Host header
    "GET http://evil.internal/steal HTTP/1.1\x0d\nHost: public.example.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8,
    -- Folded header (obs-fold, rejected per RFC 9112)
    "GET / HTTP/1.1\x0d\nHost: example.com\x0d\nX-Folded: value\x0d\n  continuation\x0d\nConnection: close\x0d\n\x0d\n".toUTF8,
  ]
  for i in [:patterns.size] do
    let pattern := patterns[i]!
    let (client, server) ← Mock.new
    let response ← sendRawAndClose client server pattern okHandler
    assertValidHttpOrEmpty s!"fuzzKnownMalicious pattern={i}" response

-- ============================================================================
-- Run all properties
-- ============================================================================

-- Property: any random byte sequence is handled safely (core libFuzzer equivalent).
#eval runWithTimeout "fuzz_random_bytes_no_panic" 30000 do
  fuzzRandomBytesNoPanic 200 0x00FACADE

-- Property: single bit mutations on valid requests are handled safely.
#eval runWithTimeout "fuzz_bit_flip_valid_requests" 30000 do
  fuzzBitFlipOnValidRequests 150 0x00B1FF10

-- Property: truncation at any byte boundary is handled safely.
#eval runWithTimeout "fuzz_truncated_requests" 30000 do
  fuzzTruncatedRequests 150 0x00DEAD42

-- Property: HTTP method prefix followed by random garbage is handled safely.
#eval runWithTimeout "fuzz_method_prefix_with_garbage" 30000 do
  fuzzMethodPrefixWithGarbage 100 0x00CA7500

-- Property: high-byte (non-ASCII) sequences are handled safely.
#eval runWithTimeout "fuzz_high_byte_values" 30000 do
  fuzzHighByteValues 120 0x00FF8000

-- Property: garbage appended after a complete request is handled safely.
#eval runWithTimeout "fuzz_garbage_after_complete_request" 30000 do
  fuzzGarbageAfterCompleteRequest 100 0x00A1B2C3

-- Property: every single-byte input is handled safely (all 256 cases).
#eval runWithTimeout "fuzz_single_byte_inputs" 30000 do
  fuzzSingleByteInputs

-- Property: known attack patterns and malformed inputs are handled safely.
#eval runWithTimeout "fuzz_known_malicious_patterns" 30000 do
  fuzzKnownMaliciousPatterns
