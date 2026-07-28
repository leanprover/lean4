import Std.Internal.SSL

/-!
Tests for `Std.Internal.SSL.Session`: in-process TLS handshake, data transfer,
and buffering behaviour driven entirely through memory BIOs (no sockets).

This is the session layer split out of #13112 (`TCP.SSL`); it builds on the
`Context` layer and is in turn used by the async `TCP.SSL` socket.
-/

open Std.Internal.SSL

-- ---------------------------------------------------------------------------
-- Helpers
-- ---------------------------------------------------------------------------

def assertEqStr (actual expected : String) : IO Unit := do
  unless actual == expected do
    throw <| IO.userError s!"expected '{expected}', got '{actual}'"

def assertGt (actual : UInt64) (bound : UInt64) (label : String) : IO Unit := do
  unless actual > bound do
    throw <| IO.userError s!"{label}: expected > {bound}, got {actual}"

def assertEqN (actual expected : UInt64) (label : String) : IO Unit := do
  unless actual == expected do
    throw <| IO.userError s!"{label}: expected {expected}, got {actual}"

-- A self-signed `CN=localhost` certificate and its matching RSA private key, embedded so the tests
-- neither shell out to `openssl` nor depend on it being installed. Valid until 2126, so peer
-- verification during the handshakes below succeeds. To regenerate:
--   openssl genrsa -out key.pem 2048
--   openssl req -new -x509 -key key.pem -out cert.pem -days 36500 -subj "/CN=localhost"
def testCertPEM : String :=
"-----BEGIN CERTIFICATE-----
MIIDCzCCAfOgAwIBAgIUfBsMFFfMmVyfKr1HjIF9ZUsOz0MwDQYJKoZIhvcNAQEL
BQAwFDESMBAGA1UEAwwJbG9jYWxob3N0MCAXDTI2MDcwNDE1NDQyNVoYDzIxMjYw
NjEwMTU0NDI1WjAUMRIwEAYDVQQDDAlsb2NhbGhvc3QwggEiMA0GCSqGSIb3DQEB
AQUAA4IBDwAwggEKAoIBAQC7SwGfQ+WLyJwnRlX37WMUEDT/YVZd0PV/6PPJSFx3
0z2vZnqMh9S7gQPvkYkon7qMtqF5jlJt3zDmddjuhhwHqeNj1htKnWPjhh8rc2DG
7v9u/36O92fz2jKUn8qHGG80+SiW4LkE8uXuC/ia0a1W03iT7rApICuSIgNrP5Zr
XZ3pHxn4m7GxnOxm/5jt0SX3HQkRV+VMEo0cGEq/8ZvmwnOOG14C/o/FxFw9zxw8
pDTabvfLVxoHCMOu7UB3c0Hg6SzM8cD/QefWQRLyD/rZIw34GcTs9IklWxJ0loqj
Y1q0c5p5991zRC2SqmM6vpAjc6dpijIAZvsycewlnY1bAgMBAAGjUzBRMB0GA1Ud
DgQWBBRam+qywW30FsQlhzW2SV7dHs96NDAfBgNVHSMEGDAWgBRam+qywW30FsQl
hzW2SV7dHs96NDAPBgNVHRMBAf8EBTADAQH/MA0GCSqGSIb3DQEBCwUAA4IBAQC7
ItNAWGWOQDfjSCi2XqbKPSMbo3d8x2fQclYuFXu3QjbsmTrkzCehvGAyXHUtbnwa
wAufdEDKjfmUZmquVQd54oTCDgNtDF4729kD7pBeIIyhWyH0osPAs9mva37ripqC
MQ3kMClzS8FSBhB03CSdkypzx0znI2rIcxbMDPCIoYtkKYyvc6/yztWZfVbhHWPC
6bYAHOFpqFCOSzcZFwzWjWmAnH+pPEX8khDTTY676VG/Yuy2F/BgCdXco8VE+kiW
hh/mZMXyGuGKuYexz8Tv5M3qzdqxNmhFObyJPk/Y7XgIoBtdyHLMkqYN5fnlUMtQ
gjuJv2wDBVKza1YhNdr1
-----END CERTIFICATE-----
"

def testKeyPEM : String :=
"-----BEGIN PRIVATE KEY-----
MIIEvQIBADANBgkqhkiG9w0BAQEFAASCBKcwggSjAgEAAoIBAQC7SwGfQ+WLyJwn
RlX37WMUEDT/YVZd0PV/6PPJSFx30z2vZnqMh9S7gQPvkYkon7qMtqF5jlJt3zDm
ddjuhhwHqeNj1htKnWPjhh8rc2DG7v9u/36O92fz2jKUn8qHGG80+SiW4LkE8uXu
C/ia0a1W03iT7rApICuSIgNrP5ZrXZ3pHxn4m7GxnOxm/5jt0SX3HQkRV+VMEo0c
GEq/8ZvmwnOOG14C/o/FxFw9zxw8pDTabvfLVxoHCMOu7UB3c0Hg6SzM8cD/QefW
QRLyD/rZIw34GcTs9IklWxJ0loqjY1q0c5p5991zRC2SqmM6vpAjc6dpijIAZvsy
cewlnY1bAgMBAAECggEADV4RnBHnAL6NMpppCVx2jViIx89lMCX5V6tDNxMEkoLP
rMSmK4CIVOek5cTf4rffwypHxRq81F2xKkmv9Xo55uwfsCD4aq9oETWh5OKDvj8R
mRUALekHkNZ6dLQg6tp6GXBNDtO0MN+7PG27TSV49zD5sqk/Bnhm07O8xbtQm5IA
LheZd4GPqBdTIf1krFNP86Th4X+DKrnuNmiXS4lDuhH/rheRfTQ4VK/srnrj//Zw
I+AeXwnch25CByXp+CoSHpwZGPYzfknZBjmkh1QbwMR/ivjA954BxbVsWl+/cAYh
7+MEvkrInJYqbwSVWQrVrKjRuHqI0OcvymBbGXoaHQKBgQDg+HBLB0Tt+mQqX+Kb
eo0ymK+V2Y0kprlVthTHPJHpA+zMcEBJWjlz0IpdfkjKAMrVoVJB4Fn8Y4Wj4Nzq
yV1AsZ/cHsH3NWnwiMaRvVTs7O60Vhs0G/I2lIx6T0dl4qWFjJQizrvMctNFVkvR
rh4tnGQnTMBViqKAB5CiW/o/dwKBgQDVIDNchhEAijUNJ60c4XcbrhGjlBmjDRyG
KfVM1LMQz9u20bZvOP/qL5wNHrlGqplOBUvD1o/J6b4ZIgzhWNB0WrPrBBi40pvv
9v7wCTZ3XfJ+KrGlWOfB0fPVs2kKjLd8b+1xoa7JM/RJIBmytXj3o9lS/6F7SkjH
0EQv086CPQKBgE83jCsPOzllMwIs01mWNMP9Oc7VVTrzrk09GWHytRpM9IQkfq6V
o6dhZmd3gWAIGWRSMunZezZBQRysoH3YPAr8wOK8veYzm8NEFk/ZUF9BKui7bUbT
FF4dvr2OzwBUZ554Gu2KyFw8jqJaucXyvtOmvymLgCpe78uPXmGda6gPAoGBAL3y
5xPtgTXD+ChzVjzJTkjjSWFLW9YQl32T48bIQ5gWSbKVEk3qtVvZdvHSkjrDTcNV
wQMYNis1InJwAJ7Pc2pgdL5fdlEzlDu5Hdp9u4eDud5s2suNg3EhWHr8XgBDDj3f
2/ZMreUxYuXRsFWwm9HKvKTWpOund1pu6nbeBc3ZAoGAWKJkhw7KoELqiCpTn3If
7ZN64vgqkNacXfjzc4D5oJ2aqAPJsTBdJ14+VShecgc5Kn0QriP0mTU712/GiK08
A0Xb02+1ouerqiUE+Ea++rZphkyC0g+MKcoCWFWKDmtJuC7vtCGLOeFuLgHahqqS
yIGPWTqB+JUmYpWBWIvu0Gg=
-----END PRIVATE KEY-----
"

-- Writes the embedded certificate and key to a per-process temporary directory, returning their paths.
def setupTestCerts : IO (String × String) := do
  let dir ← IO.FS.createTempDir
  let keyFile  := toString (dir / "key.pem")
  let certFile := toString (dir / "cert.pem")
  IO.FS.writeFile keyFile testKeyPEM
  IO.FS.writeFile certFile testCertPEM
  return (certFile, keyFile)

instance : Coe Session.Client Session := ⟨Session.Client.toSession⟩
instance : Coe Session.Server Session := ⟨Session.Server.toSession⟩

-- Drive one handshake step: advance both state machines and exchange encrypted
-- bytes between their memory BIOs. Returns (clientDone, serverDone).
def handshakeStep (c s : Session) : IO (Bool × Bool) := do
  let cd ← c.handshake
  let cOut ← c.drainEncrypted
  if cOut.size > 0 then
    discard <| s.feedEncrypted cOut
  let sd ← s.handshake
  let sOut ← s.drainEncrypted
  if sOut.size > 0 then
    discard <| c.feedEncrypted sOut
  return (cd.isNone, sd.isNone)

partial def runHandshake (c s : Session) : IO Unit := do
  let (cd, sd) ← handshakeStep c s
  unless cd && sd do runHandshake c s

-- Pipe all pending encrypted output from src into dst's read BIO.
def pipeEncrypted (src dst : Session) : IO Unit := do
  let bytes ← src.drainEncrypted
  if bytes.size > 0 then
    discard <| dst.feedEncrypted bytes

-- ---------------------------------------------------------------------------
-- Test: client configured from an in-memory PEM verifies the server cert.
-- ---------------------------------------------------------------------------

def testMkClientFromPEM (certFile keyFile : String) : IO Unit := do
  let serverCtx ← Context.Server.mk certFile keyFile

  let caPEM ← IO.FS.readFile certFile
  let clientCtx ← Context.Client.mkFromPEM caPEM true

  let serverSess ← Session.Server.mk serverCtx
  let clientSess ← Session.Client.mk clientCtx
  clientSess.setServerName "localhost"

  runHandshake clientSess serverSess

  let code ← clientSess.verifyResult
  assertEqN code 0 "verifyResult after mkFromPEM"

-- ---------------------------------------------------------------------------
-- Test: in-process TLS handshake between two memory-BIO sessions.
-- ---------------------------------------------------------------------------

def testInProcessHandshake (certFile keyFile : String) : IO Unit := do
  let serverCtx ← Context.Server.mk certFile keyFile

  let clientCtx ← Context.Client.mk "" false  -- skip peer verification

  let serverSess ← Session.Server.mk serverCtx
  let clientSess ← Session.Client.mk clientCtx

  -- setServerName exercises SSL_set_tlsext_host_name.
  clientSess.setServerName "localhost"

  runHandshake clientSess serverSess

  -- verifyResult: just verify the call succeeds (self-signed cert returns
  -- X509_V_ERR_DEPTH_ZERO_SELF_SIGNED_CERT even with VERIFY_NONE).
  discard <| clientSess.verifyResult

-- ---------------------------------------------------------------------------
-- Test: write / pendingEncrypted / drainEncrypted / feedEncrypted / read?
-- ---------------------------------------------------------------------------

def testDataTransfer (certFile keyFile : String) : IO Unit := do
  let serverCtx ← Context.Server.mk certFile keyFile

  let clientCtx ← Context.Client.mk "" false

  let serverSess ← Session.Server.mk serverCtx
  let clientSess ← Session.Client.mk clientCtx

  runHandshake clientSess serverSess

  -- write plaintext → encrypted bytes appear in the write BIO.
  let msg := "hello, tls!".toUTF8
  discard <| clientSess.write msg

  -- pendingEncrypted > 0 before draining.
  let pending ← clientSess.pendingEncrypted
  assertGt pending 0 "pendingEncrypted"

  -- Pipe to server and read back.
  pipeEncrypted clientSess serverSess
  let received ← serverSess.read? 1024
  match received with
  | .data bytes => assertEqStr (String.fromUTF8! bytes) "hello, tls!"
  | _ => throw <| IO.userError "expected data from server session"

  -- After draining, pendingEncrypted drops to 0.
  let pendingAfter ← clientSess.pendingEncrypted
  assertEqN pendingAfter 0 "pendingEncrypted after drain"

  -- read? returns wantIO when no data is available.
  let empty ← clientSess.read? 1024
  match empty with
  | .wantIO _ => return ()
  | _ => throw <| IO.userError "expected wantIO when no data available"

-- ---------------------------------------------------------------------------
-- Test: pendingPlaintext — write 100 bytes, read 10, rest stays buffered.
-- ---------------------------------------------------------------------------

def testPendingPlaintext (certFile keyFile : String) : IO Unit := do
  let serverCtx ← Context.Server.mk certFile keyFile

  let clientCtx ← Context.Client.mk "" false

  let serverSess ← Session.Server.mk serverCtx
  let clientSess ← Session.Client.mk clientCtx

  runHandshake clientSess serverSess

  let bigMsg := (String.ofList (List.replicate 100 'x')).toUTF8
  discard <| clientSess.write bigMsg
  pipeEncrypted clientSess serverSess

  -- Read only 10 bytes; the remaining 90 stay in SSL's plaintext buffer.
  discard <| serverSess.read? 10
  let remaining ← serverSess.pendingPlaintext
  assertEqN remaining 90 "pendingPlaintext after partial read"

-- ---------------------------------------------------------------------------
-- Test: empty write returns none.
-- ---------------------------------------------------------------------------

def testEmptyWrite (certFile keyFile : String) : IO Unit := do
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false

  let serverSess ← Session.Server.mk serverCtx
  let clientSess ← Session.Client.mk clientCtx
  runHandshake clientSess serverSess

  let result ← clientSess.write ByteArray.empty
  unless result.isNone do
    throw <| IO.userError "empty write should return none"

-- ---------------------------------------------------------------------------
-- Test: read? 0 returns wantIO (not .data empty) when no data is buffered.
-- ---------------------------------------------------------------------------

def testReadZero (certFile keyFile : String) : IO Unit := do
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false

  let serverSess ← Session.Server.mk serverCtx
  let clientSess ← Session.Client.mk clientCtx
  runHandshake clientSess serverSess

  -- No data has been sent; read? 0 must signal wantIO, not return .data empty.
  let result ← serverSess.read? 0
  match result with
  | .wantIO _ => return ()
  | .data b   => throw <| IO.userError s!"read? 0 returned .data (size={b.size}) instead of wantIO"
  | .closed   => throw <| IO.userError "read? 0 returned .closed unexpectedly"

-- ---------------------------------------------------------------------------
-- Test: multiple pending writes flush in order (exercises deque pop_front).
-- ---------------------------------------------------------------------------

def testPendingWriteOrder (certFile keyFile : String) : IO Unit := do
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false

  let serverSess ← Session.Server.mk serverCtx
  let clientSess ← Session.Client.mk clientCtx
  runHandshake clientSess serverSess

  -- Write three distinct messages through the client session and verify the
  -- server receives them in the same order.  This exercises the pending_writes
  -- deque: each write drains the queue front-to-back before appending.
  let msgs := #["first".toUTF8, "second".toUTF8, "third".toUTF8]
  for m in msgs do
    discard <| clientSess.write m
    pipeEncrypted clientSess serverSess

  let mut received : Array String := #[]
  for _ in msgs do
    let r ← serverSess.read? 1024
    match r with
    | .data b => received := received.push (String.fromUTF8! b)
    | _       => throw <| IO.userError "expected data in pending write order test"

  for i in List.range msgs.size do
    let expected := String.fromUTF8! msgs[i]!
    unless received[i]! == expected do
      throw <| IO.userError s!"write order mismatch at {i}: expected '{expected}', got '{received[i]!}'"

-- ---------------------------------------------------------------------------
-- Test: verifyResultString returns a non-empty string after handshake.
-- ---------------------------------------------------------------------------

def testVerifyResultString (certFile keyFile : String) : IO Unit := do
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false

  let serverSess ← Session.Server.mk serverCtx
  let clientSess ← Session.Client.mk clientCtx
  runHandshake clientSess serverSess

  let s ← clientSess.verifyResultString
  if s.isEmpty then
    throw <| IO.userError "verifyResultString returned empty string"

-- ---------------------------------------------------------------------------
-- Test: negotiatedVersion reports a modern TLS version after handshake.
-- ---------------------------------------------------------------------------

def testNegotiatedVersion (certFile keyFile : String) : IO Unit := do
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false

  let serverSess ← Session.Server.mk serverCtx
  let clientSess ← Session.Client.mk clientCtx
  runHandshake clientSess serverSess

  -- The Context layer pins a TLS 1.2 minimum, so both ends must negotiate TLSv1.2 or 1.3.
  let v ← clientSess.negotiatedVersion
  unless v == "TLSv1.3" || v == "TLSv1.2" do
    throw <| IO.userError s!"unexpected negotiated version '{v}'"
  -- Both peers must agree on the negotiated version.
  let vs ← serverSess.negotiatedVersion
  assertEqStr vs v

-- ---------------------------------------------------------------------------
-- Test: a full bidirectional close_notify exchange completes on both ends.
-- ---------------------------------------------------------------------------

-- Drive the close_notify exchange to completion, piping each side's alert to the
-- other. `fuel` bounds the loop so a regression cannot hang the test.
partial def runShutdown (fuel : Nat) (a b : Session) : IO Unit := do
  if fuel == 0 then
    throw <| IO.userError "close_notify exchange did not converge"
  let ra ← a.closeNotify
  pipeEncrypted a b
  let rb ← b.closeNotify
  pipeEncrypted b a
  unless ra.isNone && rb.isNone do runShutdown (fuel - 1) a b

def testCloseNotify (certFile keyFile : String) : IO Unit := do
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false

  let serverSess ← Session.Server.mk serverCtx
  let clientSess ← Session.Client.mk clientCtx
  runHandshake clientSess serverSess

  -- A fresh client shutdown sends its close_notify but still awaits the peer's.
  let first ← clientSess.closeNotify
  match first with
  | some .read => pure ()
  | some .write => throw <| IO.userError "initial closeNotify should await peer read, not write"
  | none => throw <| IO.userError "initial closeNotify completed before the peer responded"

  -- Pipe the alert across and run both sides to a clean bidirectional shutdown.
  pipeEncrypted clientSess serverSess
  runShutdown 16 serverSess clientSess

  -- After a clean shutdown, both report completion.
  let cDone ← clientSess.closeNotify
  let sDone ← serverSess.closeNotify
  unless cDone.isNone && sDone.isNone do
    throw <| IO.userError "closeNotify did not report a completed shutdown"

-- ---------------------------------------------------------------------------
-- Test: plaintext written before the handshake completes is queued and replayed.
-- ---------------------------------------------------------------------------

-- Calling `write` before the handshake forces SSL_write to drive the handshake, which blocks on
-- WANT_READ. The plaintext must be queued (not dropped, not failed) and delivered once the
-- handshake finishes — exercising the `pending_writes` blocked/flush path that is otherwise hard to
-- reach with always-writable memory BIOs.
def testWriteBeforeHandshake (certFile keyFile : String) : IO Unit := do
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false

  let serverSess ← Session.Server.mk serverCtx
  let clientSess ← Session.Client.mk clientCtx

  -- Write before handshaking: the data is queued, and OpenSSL asks for socket input.
  let early ← clientSess.write "early".toUTF8
  match early with
  | some .read => pure ()
  | some .write => throw <| IO.userError "write before handshake should block on read, not write"
  | none => throw <| IO.userError "write before handshake should not complete immediately"

  -- Complete the handshake; the queued plaintext stays pending throughout.
  runHandshake clientSess serverSess

  -- An empty write now flushes the queued plaintext into encrypted output.
  let flushed ← clientSess.write ByteArray.empty
  unless flushed.isNone do
    throw <| IO.userError "queued plaintext should flush cleanly after the handshake"

  pipeEncrypted clientSess serverSess
  match ← serverSess.read? 1024 with
  | .data b => assertEqStr (String.fromUTF8! b) "early"
  | _ => throw <| IO.userError "queued plaintext was not delivered after the handshake"

-- ---------------------------------------------------------------------------
-- Run all tests
-- ---------------------------------------------------------------------------

#eval do
  let (certFile, keyFile) ← setupTestCerts
  testMkClientFromPEM certFile keyFile

#eval do
  let (certFile, keyFile) ← setupTestCerts
  testInProcessHandshake certFile keyFile

#eval do
  let (certFile, keyFile) ← setupTestCerts
  testDataTransfer certFile keyFile

#eval do
  let (certFile, keyFile) ← setupTestCerts
  testPendingPlaintext certFile keyFile

#eval do
  let (certFile, keyFile) ← setupTestCerts
  testEmptyWrite certFile keyFile

#eval do
  let (certFile, keyFile) ← setupTestCerts
  testReadZero certFile keyFile

#eval do
  let (certFile, keyFile) ← setupTestCerts
  testPendingWriteOrder certFile keyFile

#eval do
  let (certFile, keyFile) ← setupTestCerts
  testVerifyResultString certFile keyFile

#eval do
  let (certFile, keyFile) ← setupTestCerts
  testNegotiatedVersion certFile keyFile

#eval do
  let (certFile, keyFile) ← setupTestCerts
  testCloseNotify certFile keyFile

#eval do
  let (certFile, keyFile) ← setupTestCerts
  testWriteBeforeHandshake certFile keyFile

/-- Returns `true` if `act` raised an `IO` exception. -/
def threw (act : IO α) : IO Bool := do
  try
    discard act; return false
  catch _ =>
    return true

-- A client that verifies the peer and pins the server's self-signed cert as its CA must still
-- reject the handshake when the requested SNI host does not match the certificate's CN/SAN.
-- This proves `setServerName` wires up hostname verification (SSL_set1_host), not just SNI.
#eval do
  let (certFile, keyFile) ← setupTestCerts
  let serverCtx ← Context.Server.mk certFile keyFile

  let caPEM ← IO.FS.readFile certFile
  let clientCtx ← Context.Client.mkFromPEM caPEM true

  let serverSess ← Session.Server.mk serverCtx
  let clientSess ← Session.Client.mk clientCtx
  -- Cert is for CN=localhost; ask for a different host.
  clientSess.setServerName "wrong.example.com"

  let threwMismatch ← threw (runHandshake clientSess serverSess)
  unless threwMismatch do
    throw <| IO.userError "handshake must fail when the SNI host does not match the certificate"

#eval do
  let (certFile, keyFile) ← setupTestCerts
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false
  let s ← Session.Server.mk serverCtx
  let c ← Session.Client.mk clientCtx
  runHandshake s.toSession c.toSession

  -- A corrupt encrypted record fed into the server's input BIO.
  let garbage := ByteArray.mk (List.replicate 64 (0x17 : UInt8)).toArray

  -- Normal read raises on the fatal record.
  discard <| s.feedEncrypted garbage
  let threwNormal ← threw (s.read? 1)

  -- The peek path (`read? 0`) must ALSO raise, not silently return `.wantIO`.
  discard <| s.feedEncrypted garbage
  let threwPeek ← threw (s.read? 0)

  unless threwNormal && threwPeek do
    throw <| IO.userError
      s!"read? must raise on a corrupt record: read? 1 threw={threwNormal}, read? 0 threw={threwPeek}"

-- A `read?` larger than one TLS record returns at most one record (16 KiB) per call, and successive
-- calls return the rest with no data loss (regression for the `read?` allocation cap).
#eval do
  let (certFile, keyFile) ← setupTestCerts
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false
  let s ← Session.Server.mk serverCtx
  let c ← Session.Client.mk clientCtx
  runHandshake s.toSession c.toSession

  let payload := ByteArray.mk ((List.replicate 100000 (0x41 : UInt8)).toArray)
  discard <| c.write payload
  pipeEncrypted c.toSession s.toSession

  -- One oversized read returns exactly one record's worth of plaintext.
  let first ← s.read? 1000000
  let firstSize := match first with | .data b => b.size | _ => 0
  assertEqN firstSize.toUInt64 16384 "first oversized read returns one record"

  -- Drain the rest; the total must equal what was written (no data lost to the cap).
  let mut total := firstSize
  let mut go := true
  while go do
    match ← s.read? 1000000 with
    | .data b => total := total + b.size
    | _ => go := false
  assertEqN total.toUInt64 100000 "total plaintext received"

-- When plaintext is already buffered (a partial read left a remainder), a subsequent oversized
-- `read?` returns exactly the buffered remainder (regression for the `SSL_pending`-based sizing).
#eval do
  let (certFile, keyFile) ← setupTestCerts
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false
  let s ← Session.Server.mk serverCtx
  let c ← Session.Client.mk clientCtx
  runHandshake s.toSession c.toSession

  -- One record's worth of plaintext, sent and decrypted via a partial read.
  let msg := "HELLO".toUTF8
  discard <| c.write msg
  pipeEncrypted c.toSession s.toSession

  -- Read only the first 2 bytes; the remaining 3 stay buffered (SSL_pending == 3).
  let part ← s.read? 2
  assertEqN (match part with | .data b => b.size.toUInt64 | _ => 0) 2 "partial read size"
  assertEqN (← s.pendingPlaintext) 3 "buffered remainder after partial read"

  -- An oversized read now returns exactly the 3 buffered bytes.
  let rest ← s.read? 1000000
  assertEqN (match rest with | .data b => b.size.toUInt64 | _ => 0) 3 "oversized read returns buffered remainder"
