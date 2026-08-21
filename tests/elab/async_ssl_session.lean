import Std.Internal.SSL
import Lean

/-!
Tests for `Std.Internal.SSL.Session`: in-process TLS handshake, data transfer,
and buffering behaviour driven entirely through memory BIOs (no sockets).

This is the session layer split out of #13112 (`TCP.SSL`); it builds on the
`Context` layer and is in turn used by the async `TCP.SSL` socket.
-/

open Std.Internal.SSL

open Lean in

elab "include_cert% " path:str : term => do
  let dir := (System.FilePath.mk (← readThe Core.Context).fileName).parent.getD ⟨"."⟩
  return mkStrLit (← IO.FS.readFile (dir / path.getString))

def assertEqStr (actual expected : String) : IO Unit := do
  unless actual == expected do
    throw <| IO.userError s!"expected '{expected}', got '{actual}'"

def assertGt (actual : UInt64) (bound : UInt64) (label : String) : IO Unit := do
  unless actual > bound do
    throw <| IO.userError s!"{label}: expected > {bound}, got {actual}"

def assertEqN (actual expected : UInt64) (label : String) : IO Unit := do
  unless actual == expected do
    throw <| IO.userError s!"{label}: expected {expected}, got {actual}"

def testCertPEM : String := include_cert% "async_ssl_certs/cert.pem"

def testKeyPEM : String := include_cert% "async_ssl_certs/key.pem"

def setupTestCerts : IO (String × String) := do
  let dir ← IO.FS.createTempDir
  let keyFile := toString (dir / "key.pem")
  let certFile := toString (dir / "cert.pem")
  IO.FS.writeFile keyFile testKeyPEM
  IO.FS.writeFile certFile testCertPEM
  return (certFile, keyFile)

instance : Coe Session.Client Session := ⟨Session.Client.toSession⟩
instance : Coe Session.Server Session := ⟨Session.Server.toSession⟩

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

def pipeEncrypted (src dst : Session) : IO Unit := do
  let bytes ← src.drainEncrypted
  if bytes.size > 0 then
    discard <| dst.feedEncrypted bytes

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

def testInProcessHandshake (certFile keyFile : String) : IO Unit := do
  let serverCtx ← Context.Server.mk certFile keyFile

  let clientCtx ← Context.Client.mk "" false

  let serverSess ← Session.Server.mk serverCtx
  let clientSess ← Session.Client.mk clientCtx

  clientSess.setServerName "localhost"
  runHandshake clientSess serverSess
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
-- Test: queued writes reach the peer in the order they were made.
-- ---------------------------------------------------------------------------

-- Memory BIOs are always writable, so a post-handshake `SSL_write` never blocks and never queues.
-- Writing before the handshake is what fills `pending_writes`, making this an ordering test of the
-- queue rather than of TLS record delivery.
def testPendingWriteOrder (certFile keyFile : String) : IO Unit := do
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false

  let serverSess ← Session.Server.mk serverCtx
  let clientSess ← Session.Client.mk clientCtx

  let msgs := #["first", "second", "third"]
  for m in msgs do
    match ← clientSess.write m.toUTF8 with
    | some .read => pure ()
    | some .write => throw <| IO.userError s!"queueing '{m}' should block on read, not write"
    | none => throw <| IO.userError s!"'{m}' was taken immediately, so the queue is left untested"

  runHandshake clientSess serverSess

  -- The empty write flushes the whole queue; the peer must see one stream in the original order.
  unless (← clientSess.write ByteArray.empty).isNone do
    throw <| IO.userError "the queued plaintext did not flush after the handshake"
  pipeEncrypted clientSess serverSess

  let expected := String.join msgs.toList
  let mut received := ""
  for _ in msgs do
    if received.length < expected.length then
      match ← serverSess.read? 1024 with
      | .data b => received := received ++ String.fromUTF8! b
      | _ => throw <| IO.userError s!"expected more queued plaintext, got '{received}'"

  unless received == expected do
    throw <| IO.userError s!"write order mismatch: expected '{expected}', got '{received}'"

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
-- Test: a close_notify arriving behind unread application data.
-- ---------------------------------------------------------------------------

-- A peer may send its last application record and its `close_notify` in a single flight, so both
-- land in the input BIO together. Starting our own shutdown at that point must neither consume nor
-- reject the record: `closeNotify` reports `none` — our alert is out and the peer's sits behind
-- plaintext that no socket I/O can carry us past — `read?` hands the record out and only then
-- reports `.closed`, and a further `closeNotify` completes the shutdown.
--
-- OpenSSL rejects an application record read *inside* `SSL_shutdown` as a fatal protocol error
-- (`application data after close notify`), so the runtime peeks before letting the shutdown read.

def testCloseNotifyWithPendingData (certFile keyFile : String) : IO Unit := do
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false

  let serverSess ← Session.Server.mk serverCtx
  let clientSess ← Session.Client.mk clientCtx
  runHandshake clientSess serverSess

  -- Deliver a final application record and the server's close_notify together.
  discard <| serverSess.write "final".toUTF8
  let serverClosing ← serverSess.closeNotify
  match serverClosing with
  | some .read => pure ()
  | some .write => throw <| IO.userError "server closeNotify should await peer input"
  | none => throw <| IO.userError "server closeNotify completed before the peer responded"
  pipeEncrypted serverSess clientSess

  -- Initiating our side of the shutdown must not consume or reject the unread application record
  -- that precedes the peer's close_notify. The alert is already buffered behind that record, so no
  -- socket input is outstanding and asking for some would strand a caller that loops on this alone.
  let clientClosing ← clientSess.closeNotify
  match clientClosing with
  | none => pure ()
  | r => throw <| IO.userError s!"client closeNotify asked for input that had already arrived, got {repr r}"

  match ← clientSess.read? 1024 with
  | .data bytes => assertEqStr (String.fromUTF8! bytes) "final"
  | .wantIO _ => throw <| IO.userError "expected final application data before close_notify"
  | .closed => throw <| IO.userError "close_notify was reported before final application data"

  match ← clientSess.read? 1024 with
  | .closed => pure ()
  | .data _ => throw <| IO.userError "unexpected application data after final record"
  | .wantIO _ => throw <| IO.userError "expected buffered close_notify after final record"

  -- Nothing is left undelivered, so the client's shutdown now completes.
  let clientDone ← clientSess.closeNotify
  unless clientDone.isNone do
    throw <| IO.userError "client shutdown did not complete after the peer's close_notify was read"

  pipeEncrypted clientSess serverSess
  let serverDone ← serverSess.closeNotify

  unless serverDone.isNone do
    throw <| IO.userError "server shutdown did not complete after receiving close_notify"

-- ---------------------------------------------------------------------------
-- Test: closing while the peer's plaintext is unread and its alert has not arrived.
-- ---------------------------------------------------------------------------

-- The same shutdown-before-drain race, but the peer has only sent data so far: there is no buffered
-- `close_notify` to finish on. `closeNotify` must send our alert and keep the plaintext intact for
-- as many calls as it takes — a session with undelivered data must survive an early shutdown rather
-- than fail, and must never report an `IOWant` for input that cannot advance it.
def testCloseNotifyBeforeDrainingData (certFile keyFile : String) : IO Unit := do
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false

  let serverSess ← Session.Server.mk serverCtx
  let clientSess ← Session.Client.mk clientCtx
  runHandshake clientSess serverSess

  discard <| serverSess.write "final".toUTF8
  pipeEncrypted serverSess clientSess

  for attempt in [1, 2] do
    match ← clientSess.closeNotify with
    | none => pure ()
    | r => throw <| IO.userError s!"closeNotify {attempt} asked for input it could not use, got {repr r}"

  match ← clientSess.read? 1024 with
  | .data bytes => assertEqStr (String.fromUTF8! bytes) "final"
  | .wantIO _ => throw <| IO.userError "unread plaintext was consumed by closeNotify"
  | .closed => throw <| IO.userError "session reported closed with plaintext still unread"

  -- The peer answers our alert; both ends then reach a clean shutdown.
  pipeEncrypted clientSess serverSess
  let serverDone ← serverSess.closeNotify
  unless serverDone.isNone do
    throw <| IO.userError "server shutdown did not complete after receiving close_notify"

  pipeEncrypted serverSess clientSess
  let clientDone ← clientSess.closeNotify
  unless clientDone.isNone do
    throw <| IO.userError "client shutdown did not complete after receiving close_notify"

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
-- Test: `read?` reports which socket I/O it is actually waiting on.
-- ---------------------------------------------------------------------------

-- `ReadResult.wantIO` stores its `IOWant` unboxed, unlike the `Option IOWant` the other primitives
-- return, so the two are built differently on the C side. A session with an empty input BIO must
-- report `.read` — reporting `.write` would send an event loop to wait for writability that is
-- always immediately true, spinning instead of waiting for the peer.
def testReadWantIO (certFile keyFile : String) : IO Unit := do
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false

  let serverSess ← Session.Server.mk serverCtx
  let clientSess ← Session.Client.mk clientCtx

  let expectWantRead (r : ReadResult) (label : String) : IO Unit :=
    match r with
    | .wantIO .read => pure ()
    | .wantIO .write => throw <| IO.userError s!"{label}: expected wantIO .read, got .write"
    | .data b => throw <| IO.userError s!"{label}: expected wantIO .read, got data ({b.size} bytes)"
    | .closed => throw <| IO.userError s!"{label}: expected wantIO .read, got closed"

  -- Before the handshake, and again after the ClientHello has been drained, the session is waiting
  -- on encrypted input in both the peek and the sized-read paths.
  expectWantRead (← clientSess.read? 0) "peek before handshake"
  expectWantRead (← clientSess.read? 1024) "read before handshake"
  let hello ← clientSess.drainEncrypted
  expectWantRead (← clientSess.read? 0) "peek after draining ClientHello"
  expectWantRead (← clientSess.read? 1024) "read after draining ClientHello"

  -- Once the handshake is done and no plaintext is buffered, it is still input we are waiting for.
  discard <| serverSess.feedEncrypted hello
  runHandshake clientSess serverSess
  expectWantRead (← clientSess.read? 0) "peek after handshake"
  expectWantRead (← clientSess.read? 1024) "read after handshake"
  expectWantRead (← serverSess.read? 1024) "server read after handshake"

-- ---------------------------------------------------------------------------
-- Run all tests
-- ---------------------------------------------------------------------------

#eval do
  let (certFile, keyFile) ← setupTestCerts
  testMkClientFromPEM certFile keyFile

#eval do
  let (certFile, keyFile) ← setupTestCerts
  testReadWantIO certFile keyFile

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
  testCloseNotifyWithPendingData certFile keyFile

#eval do
  let (certFile, keyFile) ← setupTestCerts
  testCloseNotifyBeforeDrainingData certFile keyFile

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

  -- A corrupt encrypted record fed into the server's input BIO. The record is fatal, so each path
  -- needs its own session: the torn-down one refuses further input.
  let corrupted : IO Session.Server := do
    let s ← Session.Server.mk serverCtx
    let c ← Session.Client.mk clientCtx
    runHandshake s.toSession c.toSession
    discard <| s.feedEncrypted (ByteArray.mk (List.replicate 64 (0x17 : UInt8)).toArray)
    return s

  -- Normal read raises on the fatal record.
  let threwNormal ← threw ((← corrupted).read? 1)

  -- The peek path (`read? 0`) must ALSO raise, not silently return `.wantIO`.
  let threwPeek ← threw ((← corrupted).read? 0)

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
-- `read?` returns exactly the buffered remainder rather than a full record.
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

-- ---------------------------------------------------------------------------
-- Regression tests for the fixes below.
-- ---------------------------------------------------------------------------

/-- Runs `act` and returns the raised `IO` exception's message, or `none` if it succeeded. -/
def errorOf (act : IO α) : IO (Option String) := do
  try
    discard act; return none
  catch e =>
    return some (toString e)

-- `closeNotify` owns the pending-write queue: plaintext `write` accepted must reach the peer before
-- the alert that ends the session, with no explicit flush from the caller. A write issued before the
-- handshake blocks on WANT_READ, which is the only way to get plaintext queued behind memory BIOs.
#eval do
  let (certFile, keyFile) ← setupTestCerts
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false
  let s ← Session.Server.mk serverCtx
  let c ← Session.Client.mk clientCtx

  discard <| c.write "queued-payload".toUTF8
  runHandshake c.toSession s.toSession

  -- No explicit `write ByteArray.empty` flush: `closeNotify` is responsible for the queue.
  discard <| c.closeNotify
  pipeEncrypted c.toSession s.toSession

  match ← s.read? 1024 with
  | .data b => assertEqStr (String.fromUTF8! b) "queued-payload"
  | .closed => throw <| IO.userError "closeNotify dropped the plaintext queued by write"
  | .wantIO _ => throw <| IO.userError "expected the queued plaintext, got wantIO"

-- Once a record has been rejected as fatally malformed, OpenSSL answers every further operation with
-- a bare `SSL_ERROR_SYSCALL` — no alert is involved, the session is torn down locally. Both BIOs are
-- memory BIOs, so that is never a transport EOF, and an aborted session must not be reported as
-- `end of file` — a caller would read that as a clean end of stream.
#eval do
  let (certFile, keyFile) ← setupTestCerts
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false
  let s ← Session.Server.mk serverCtx
  let c ← Session.Client.mk clientCtx
  runHandshake s.toSession c.toSession

  discard <| s.feedEncrypted (ByteArray.mk (List.replicate 64 (0x17 : UInt8)).toArray)
  let first ← errorOf (s.read? 128)
  unless first.isSome do
    throw <| IO.userError "a corrupt record must raise"

  let after : List (String × IO Unit) :=
    [("read?", discard <| s.read? 128),
     ("write", discard <| s.write "x".toUTF8),
     ("handshake", discard <| s.handshake)]

  for (label, act) in after do
    match ← errorOf act with
    | none => throw <| IO.userError s!"{label} after a fatal error should still raise"
    | some msg =>
      if (msg.splitOn "end of file").length > 1 then
        throw <| IO.userError s!"{label} after a fatal error reported EOF: {msg}"

-- `read?` and `handshake` short-circuit on the recorded failure and never touch the input BIO again,
-- so bytes fed to an aborted session are never consumed. Reporting success for them would let a
-- transport pump grow the BIO without bound while the caller is told the data was accepted.
#eval do
  let (certFile, keyFile) ← setupTestCerts
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false
  let s ← Session.Server.mk serverCtx
  let c ← Session.Client.mk clientCtx
  runHandshake s.toSession c.toSession

  discard <| s.feedEncrypted (ByteArray.mk (List.replicate 64 (0x17 : UInt8)).toArray)
  unless (← errorOf (s.read? 128)).isSome do
    throw <| IO.userError "a corrupt record must raise"

  let chunk := ByteArray.mk (List.replicate 1024 (0x58 : UInt8)).toArray
  for i in [0, 1, 2] do
    match ← errorOf (s.feedEncrypted chunk) with
    | none =>
      throw <| IO.userError
        s!"feedEncrypted #{i} on an aborted session reported success; those bytes are never consumed"
    | some msg =>
      if (msg.splitOn "end of file").length > 1 then
        throw <| IO.userError s!"feedEncrypted after a fatal error reported EOF: {msg}"

-- A corrupt record on an established session reports a wrong record version, which is not the same
-- condition as a peer that cannot negotiate a TLS version.
#eval do
  let (certFile, keyFile) ← setupTestCerts
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false
  let s ← Session.Server.mk serverCtx
  let c ← Session.Client.mk clientCtx
  runHandshake s.toSession c.toSession

  discard <| s.feedEncrypted (ByteArray.mk (List.replicate 64 (0x17 : UInt8)).toArray)
  match ← errorOf (s.read? 128) with
  | none => throw <| IO.userError "a corrupt record must raise"
  | some msg =>
    unless (msg.splitOn "unrecognized version").length > 1 do
      throw <| IO.userError s!"unexpected corrupt-record message: {msg}"

-- Plaintext HTTP reaching a TLS port is the most common way a server meets a peer that is not
-- speaking TLS, and OpenSSL diagnoses it specifically rather than as a bad record version. Naming it
-- is what distinguishes a misdirected client from a genuine handshake failure.
#eval do
  let (certFile, keyFile) ← setupTestCerts
  let serverCtx ← Context.Server.mk certFile keyFile
  let s ← Session.Server.mk serverCtx

  discard <| s.feedEncrypted "GET / HTTP/1.1\r\nHost: example.com\r\n\r\n".toUTF8
  match ← errorOf s.handshake with
  | none => throw <| IO.userError "an HTTP request must fail the TLS handshake"
  | some msg =>
    unless (msg.splitOn "plaintext HTTP request").length > 1 do
      throw <| IO.userError s!"unexpected HTTP-to-TLS message: {msg}"

-- SNI and the hostname check both travel with the handshake, so setting a server name afterwards
-- cannot take effect and must be rejected instead of silently succeeding.
#eval do
  let (certFile, keyFile) ← setupTestCerts
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false
  let s ← Session.Server.mk serverCtx
  let c ← Session.Client.mk clientCtx
  runHandshake c.toSession s.toSession

  match ← errorOf (c.setServerName "evil.example.com") with
  | none => throw <| IO.userError "setServerName after the handshake must be rejected"
  | some msg =>
    unless (msg.splitOn "before the handshake").length > 1 do
      throw <| IO.userError s!"unexpected setServerName error: {msg}"

-- A session that never handshaked has nothing to close, so teardown must not raise. Repeated calls
-- stay a no-op.
#eval do
  let clientCtx ← Context.Client.mk "" false
  let c ← Session.Client.mk clientCtx
  for i in [0, 1, 2] do
    match ← errorOf c.closeNotify with
    | none => pure ()
    | some msg => throw <| IO.userError s!"closeNotify #{i} on a fresh session raised: {msg}"

-- Reporting a clean close has to end the session: a fatal error also puts one back in init, so the
-- branch that reports "nothing to tear down" cannot leave it looking ready to negotiate.
#eval do
  let clientCtx ← Context.Client.mk "" false
  let c ← Session.Client.mk clientCtx
  discard <| c.closeNotify

  let after : List (String × IO Unit) :=
    [("handshake", discard <| c.handshake),
     ("write", discard <| c.write "x".toUTF8),
     ("read?", discard <| c.read? 128),
     ("feedEncrypted", discard <| c.feedEncrypted "x".toUTF8)]

  -- The session is finished, but nothing fatal ever happened to it: reporting one would send a
  -- caller hunting for a protocol failure that only its own teardown caused.
  for (label, act) in after do
    match ← errorOf act with
    | none => throw <| IO.userError s!"{label} drove a session that closeNotify already reported closed"
    | some msg =>
      unless (msg.splitOn "closed before it was negotiated").length > 1 do
        throw <| IO.userError s!"{label} on a session closed before negotiating reported: {msg}"

-- The same holds once a fatal error has torn the session down: the shutdown has nothing left to do.
#eval do
  let (certFile, keyFile) ← setupTestCerts
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false
  let s ← Session.Server.mk serverCtx
  let c ← Session.Client.mk clientCtx
  runHandshake s.toSession c.toSession

  discard <| s.feedEncrypted (ByteArray.mk (List.replicate 64 (0x17 : UInt8)).toArray)
  discard <| errorOf (s.read? 128)
  match ← errorOf s.closeNotify with
  | none => pure ()
  | some msg => throw <| IO.userError s!"closeNotify on an aborted session raised: {msg}"

-- A session that never negotiated cannot carry plaintext `write` accepted, and flushing it would run
-- the handshake rather than complete a teardown. The data is lost either way, so the shutdown says
-- so instead of reporting the clean close it reports when nothing was pending.
#eval do
  let clientCtx ← Context.Client.mk "" false
  let c ← Session.Client.mk clientCtx
  discard <| c.write "never-sent".toUTF8
  match ← errorOf c.closeNotify with
  | none => throw <| IO.userError "closeNotify reported a clean close while dropping queued plaintext"
  | some msg =>
    unless (msg.splitOn "before buffered data could be sent").length > 1 do
      throw <| IO.userError s!"unexpected closeNotify error: {msg}"

-- The same holds when the session was established and then torn down by a fatal error: a queue that
-- survives the abort must not be reported as a clean close. A write issued before the handshake is
-- the only way to still be holding plaintext once the session is up.
#eval do
  let (certFile, keyFile) ← setupTestCerts
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false
  let s ← Session.Server.mk serverCtx
  let c ← Session.Client.mk clientCtx

  discard <| c.write "queued-payload".toUTF8
  runHandshake c.toSession s.toSession

  discard <| c.feedEncrypted (ByteArray.mk (List.replicate 64 (0x17 : UInt8)).toArray)
  discard <| errorOf (c.read? 128)

  match ← errorOf c.closeNotify with
  | none => throw <| IO.userError "closeNotify reported a clean close on an aborted session with queued plaintext"
  | some msg =>
    unless (msg.splitOn "before buffered data could be sent").length > 1 do
      throw <| IO.userError s!"unexpected closeNotify error: {msg}"

-- `closeNotify` decides "this session never negotiated, so there is nothing to close" from the
-- session's own handshake state rather than from whatever the failing `SSL_shutdown` happened to
-- leave in the error queue. A half-open handshake is the case that distinguishes the two: the
-- ClientHello has been produced, so the session is no longer untouched, but it is still in init.
#eval do
  let clientCtx ← Context.Client.mk "" false
  let c ← Session.Client.mk clientCtx
  discard <| c.handshake
  discard <| c.drainEncrypted
  match ← errorOf c.closeNotify with
  | none => pure ()
  | some msg => throw <| IO.userError s!"closeNotify mid-handshake raised: {msg}"

-- `read?` reports the socket I/O the *queue* is waiting on, never one it invented: a blocked flush
-- supersedes the read's own want. Plaintext written before the handshake is the only way to hold a
-- blocked queue behind memory BIOs, and there OpenSSL wants encrypted input for both.
#eval do
  let clientCtx ← Context.Client.mk "" false
  let c ← Session.Client.mk clientCtx
  discard <| c.write "queued".toUTF8
  for (label, r) in [("peek", ← c.read? 0), ("read", ← c.read? 1024)] do
    match r with
    | .wantIO .read => pure ()
    | .wantIO .write => throw <| IO.userError s!"{label} with a blocked queue reported .write"
    | .data b => throw <| IO.userError s!"{label} returned data ({b.size} bytes) before the handshake"
    | .closed => throw <| IO.userError s!"{label} reported closed before the handshake"

-- The pending-write queue is bounded, so a caller that keeps writing while the session is blocked
-- is refused rather than allowed to buffer without limit. The first write is always admitted: a
-- blocked `SSL_write` consumed nothing but requires the same bytes and length back on retry, so
-- that payload has to be kept whatever its size.
#eval do
  let clientCtx ← Context.Client.mk "" false
  let c ← Session.Client.mk clientCtx
  let chunk : ByteArray := ⟨Array.replicate (128 * 1024) (0x41 : UInt8)⟩

  let mut refused := none
  for _ in [0:16] do
    if refused.isNone then
      refused := ← errorOf (c.write chunk)

  match refused with
  | none => throw <| IO.userError "the pending-write queue accepted 2 MiB without a bound"
  | some msg =>
    unless (msg.splitOn "maximum amount of unsent plaintext").length > 1 do
      throw <| IO.userError s!"unexpected queue-full error: {msg}"

-- Until the transport reports EOF, an empty input BIO is indistinguishable from "the next bytes
-- have not arrived yet", so a peer that vanishes without `close_notify` would leave `read?` asking
-- for input forever. `feedEof` turns that into the truncation error it actually is.
#eval do
  let (certFile, keyFile) ← setupTestCerts
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false
  let s ← Session.Server.mk serverCtx
  let c ← Session.Client.mk clientCtx
  runHandshake c.toSession s.toSession

  match ← c.read? 128 with
  | .wantIO .read => pure ()
  | _ => throw <| IO.userError "expected the client to be waiting on input before feedEof"

  c.feedEof
  match ← errorOf (c.read? 128) with
  | none => throw <| IO.userError "read? after feedEof must report the truncated stream"
  | some msg =>
    unless (msg.splitOn "end of file").length > 1 do
      throw <| IO.userError s!"unexpected feedEof error: {msg}"

  -- The stream is over, so further encrypted input is a caller error rather than a silent resume.
  match ← errorOf (c.feedEncrypted "late".toUTF8) with
  | none => throw <| IO.userError "feedEncrypted after feedEof must be rejected"
  | some msg =>
    unless (msg.splitOn "already ended").length > 1 do
      throw <| IO.userError s!"unexpected feedEncrypted-after-feedEof error: {msg}"

-- `feedEof` marks the end of the stream, not the end of what has been read: bytes already fed stay
-- readable, and a `close_notify` among them still ends the session cleanly rather than as a
-- truncation.
#eval do
  let (certFile, keyFile) ← setupTestCerts
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false
  let s ← Session.Server.mk serverCtx
  let c ← Session.Client.mk clientCtx
  runHandshake c.toSession s.toSession

  discard <| s.write "last".toUTF8
  discard <| s.closeNotify
  pipeEncrypted s.toSession c.toSession
  c.feedEof

  match ← c.read? 1024 with
  | .data b => assertEqStr (String.fromUTF8! b) "last"
  | .closed => throw <| IO.userError "feedEof discarded plaintext that had already been fed"
  | .wantIO _ => throw <| IO.userError "expected the buffered record after feedEof"

  match ← c.read? 1024 with
  | .closed => pure ()
  | .data b => throw <| IO.userError s!"unexpected data ({b.size} bytes) after the peer's close_notify"
  | .wantIO _ => throw <| IO.userError "expected .closed for a close_notify received before feedEof"

-- A single `write` larger than the queue bound is admitted, since `SSL_write` has already taken the
-- payload by then. The bound still has to hold for everything written afterwards, even though the
-- queue is now sitting above it.
#eval do
  let clientCtx ← Context.Client.mk "" false
  let c ← Session.Client.mk clientCtx

  discard <| c.write ⟨Array.replicate (2 * 1024 * 1024) (0x41 : UInt8)⟩

  let chunk : ByteArray := ⟨Array.replicate (64 * 1024) (0x41 : UInt8)⟩
  let mut refused := none
  for _ in [0:8] do
    if refused.isNone then
      refused := ← errorOf (c.write chunk)

  match refused with
  | none => throw <| IO.userError "an oversized queued write disabled the pending-write bound"
  | some msg =>
    unless (msg.splitOn "maximum amount of unsent plaintext").length > 1 do
      throw <| IO.userError s!"unexpected queue-full error: {msg}"

  -- A full queue must still accept the empty write that exists to drain it, or there would be no
  -- way back from the bound.
  match ← errorOf (c.write ByteArray.empty) with
  | none => pure ()
  | some msg => throw <| IO.userError s!"a full queue refused a pure flush: {msg}"

-- The server name feeds the `ClientHello`, so it is too late to set once the handshake has started
-- even though the session is not yet established: SNI would go unsent while the caller was told it
-- had been applied.
#eval do
  let clientCtx ← Context.Client.mk "" false
  let c ← Session.Client.mk clientCtx
  discard <| c.handshake

  match ← errorOf (c.setServerName "example.com") with
  | none => throw <| IO.userError "setServerName was accepted after the ClientHello had been sent"
  | some msg =>
    unless (msg.splitOn "before the handshake starts").length > 1 do
      throw <| IO.userError s!"unexpected setServerName error: {msg}"

-- OpenSSL diagnoses a truncated stream once and then reports the session as a generic failure, so
-- the truncation has to be remembered: every `read?` after the transport ends must agree.
#eval do
  let (certFile, keyFile) ← setupTestCerts
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false
  let s ← Session.Server.mk serverCtx
  let c ← Session.Client.mk clientCtx
  runHandshake c.toSession s.toSession

  c.feedEof
  for label in ["read", "repeated read", "peek"] do
    let r ← errorOf (if label == "peek" then c.read? 0 else c.read? 1024)
    match r with
    | none => throw <| IO.userError s!"{label} after feedEof did not raise"
    | some msg =>
      unless (msg.splitOn "end of file").length > 1 do
        throw <| IO.userError s!"{label} after feedEof reported '{msg}' instead of end of file"

-- Teardown runs on exactly the connections whose peer vanishes without answering our alert, so a
-- transport that ends there is the expected outcome rather than an error to catch.
#eval do
  let (certFile, keyFile) ← setupTestCerts
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false
  let s ← Session.Server.mk serverCtx
  let c ← Session.Client.mk clientCtx
  runHandshake c.toSession s.toSession

  match ← c.closeNotify with
  | some .read => pure ()
  | r => throw <| IO.userError s!"expected to be waiting for the peer's close_notify, got {repr r}"

  discard <| c.drainEncrypted
  c.feedEof

  for i in [0:3] do
    match ← errorOf c.closeNotify with
    | none => pure ()
    | some msg => throw <| IO.userError s!"closeNotify #{i} after a half-close raised: {msg}"

-- A peer's `close_notify` sent behind a final record is buffered the moment that flight arrives, but
-- OpenSSL cannot report it without consuming the record first — and a shutdown must not consume
-- plaintext. Reporting `.read` there would strand a caller looping on `closeNotify` alone: the alert
-- it is told to wait for has already arrived, so no further input can ever come. Looping on
-- `closeNotify` must terminate whether or not the caller interleaves `read?`.
#eval do
  let (certFile, keyFile) ← setupTestCerts
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false
  let s ← Session.Server.mk serverCtx
  let c ← Session.Client.mk clientCtx
  runHandshake c.toSession s.toSession

  discard <| s.write "final-record".toUTF8
  discard <| s.closeNotify
  discard <| c.feedEncrypted (← s.drainEncrypted)

  for i in [0:3] do
    match ← c.closeNotify with
    | none => pure ()
    | r => throw <| IO.userError s!"closeNotify #{i} asked for input that had already arrived: {repr r}"

  -- The shutdown reported done, but the plaintext behind which the alert sat is still there.
  match ← c.read? 1024 with
  | .data b => assertEqStr (String.fromUTF8! b) "final-record"
  | .closed => throw <| IO.userError "closeNotify discarded the plaintext it stopped short of"
  | .wantIO _ => throw <| IO.userError "expected the buffered plaintext after the shutdown"

  -- Draining the rest reaches the peer's alert, completing the bidirectional shutdown.
  match ← c.read? 1024 with
  | .closed => pure ()
  | _ => throw <| IO.userError "expected the peer's close_notify behind the record"

  match ← c.closeNotify with
  | none => pure ()
  | r => throw <| IO.userError s!"shutdown did not complete after the alert was read, got {repr r}"

-- A fatal error is diagnosed by OpenSSL exactly once; afterwards `SSL_in_init`, `SSL_get_shutdown`
-- and `SSL_want` read the same as on a session that is merely waiting for input, so an undefended
-- retry is told to wait for socket I/O that can never arrive. Every operation must keep reporting
-- the failure instead. The garbage below is chosen for the record header OpenSSL rejects without
-- leaving anything queued, which is the case that degrades; other malformed input re-raises by
-- itself and would not exercise this.
#eval do
  let (certFile, keyFile) ← setupTestCerts
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false
  let s ← Session.Server.mk serverCtx
  let c ← Session.Client.mk clientCtx

  -- The client is waiting for a ServerHello; hand it a record with an unusable version instead.
  discard <| c.handshake
  discard <| s.feedEncrypted (← c.drainEncrypted)
  discard <| c.feedEncrypted (ByteArray.mk (List.replicate 64 (0x16 : UInt8)).toArray)

  match ← errorOf c.handshake with
  | none => throw <| IO.userError "a bogus record must fail the handshake"
  | some msg =>
    unless (msg.splitOn "unrecognized version").length > 1 do
      throw <| IO.userError s!"unexpected handshake error: {msg}"

  -- The session is dead. Nothing may report progress or ask for input again.
  let after : List (String × IO String) :=
    [("handshake", do let r ← c.handshake; return s!"{repr r}"),
     ("write", do let r ← c.write "x".toUTF8; return s!"{repr r}"),
     ("read?", do let r ← c.read? 1024; return s!"{repr (r matches .closed)}")]

  for (label, act) in after do
    for i in [0:3] do
      match ← errorOf act with
      | none => throw <| IO.userError s!"{label} #{i} returned instead of reporting the fatal error"
      | some msg =>
        unless (msg.splitOn "aborted by an earlier fatal error").length > 1 do
          throw <| IO.userError s!"{label} #{i} reported '{msg}'"

-- A truncated stream keeps its own classification: `failed` alone would turn the end of the stream
-- into a protocol error, which a caller cannot distinguish from a peer that spoke garbage.
#eval do
  let (certFile, keyFile) ← setupTestCerts
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false
  let s ← Session.Server.mk serverCtx
  let c ← Session.Client.mk clientCtx
  runHandshake c.toSession s.toSession
  c.feedEof

  for label in ["read", "repeated read", "handshake"] do
    let r ← errorOf (if label == "handshake" then discard c.handshake else discard (c.read? 1024))
    match r with
    | none => throw <| IO.userError s!"{label} after feedEof did not raise"
    | some msg =>
      unless (msg.splitOn "end of file").length > 1 do
        throw <| IO.userError s!"{label} after feedEof reported '{msg}' instead of end of file"

-- Teardown must not depend on whether the caller happened to read first. The same broken session
-- reaches `closeNotify` by two routes -- with the failure already diagnosed, and with `closeNotify`
-- itself the first call to touch the bad input -- and both must report the same clean close.
#eval do
  let mk : IO Session.Server := do
    let (certFile, keyFile) ← setupTestCerts
    let serverCtx ← Context.Server.mk certFile keyFile
    let clientCtx ← Context.Client.mk "" false
    let s ← Session.Server.mk serverCtx
    let c ← Session.Client.mk clientCtx
    runHandshake c.toSession s.toSession
    discard <| s.feedEncrypted (ByteArray.mk (List.replicate 64 (0x17 : UInt8)).toArray)
    return s

  -- Route A: a read diagnoses the corrupt record, then teardown runs.
  let a ← mk
  discard <| errorOf (a.read? 1024)
  match ← errorOf a.closeNotify with
  | none => pure ()
  | some msg => throw <| IO.userError s!"closeNotify raised after the failure was diagnosed: {msg}"

  -- Route B: teardown is the first call to see the corrupt record.
  let b ← mk
  match ← errorOf b.closeNotify with
  | none => pure ()
  | some msg => throw <| IO.userError s!"closeNotify raised on an undiagnosed failure: {msg}"

  -- Both sessions stay torn down, and repeated teardown stays a no-op.
  for (label, sess) in [("A", a), ("B", b)] do
    for i in [0:2] do
      match ← errorOf sess.closeNotify with
      | none => pure ()
      | some msg => throw <| IO.userError s!"closeNotify {label} #{i} raised: {msg}"

-- The one loss a caller has to hear about on teardown is plaintext `write` accepted but never
-- delivered, and a session killed before it could be flushed is exactly that case.
#eval do
  let (certFile, keyFile) ← setupTestCerts
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false
  let s ← Session.Server.mk serverCtx
  let c ← Session.Client.mk clientCtx

  -- Queued before the handshake, so it is still waiting when the session dies.
  match ← c.write "never-sent".toUTF8 with
  | some _ => pure ()
  | none => throw <| IO.userError "a pre-handshake write should be queued, not accepted outright"

  discard <| s.feedEncrypted (← c.drainEncrypted)
  discard <| c.feedEncrypted (ByteArray.mk (List.replicate 64 (0x16 : UInt8)).toArray)
  discard <| errorOf c.handshake

  match ← errorOf c.closeNotify with
  | none => throw <| IO.userError "closeNotify silently dropped plaintext accepted by write"
  | some msg =>
    unless (msg.splitOn "before buffered data could be sent").length > 1 do
      throw <| IO.userError s!"unexpected closeNotify error: {msg}"

-- Reporting undelivered plaintext is what a teardown path has to hear, but only once: a `finally`
-- or a retry loop calls `closeNotify` again, and a session that has already reported the loss has
-- nothing left to say about it.
#eval do
  let clientCtx ← Context.Client.mk "" false
  let c ← Session.Client.mk clientCtx
  discard <| c.write "never-sent".toUTF8

  match ← errorOf c.closeNotify with
  | none => throw <| IO.userError "closeNotify reported a clean close while dropping queued plaintext"
  | some msg =>
    unless (msg.splitOn "before buffered data could be sent").length > 1 do
      throw <| IO.userError s!"unexpected closeNotify error: {msg}"

  for i in [0:3] do
    match ← errorOf c.closeNotify with
    | none => pure ()
    | some msg => throw <| IO.userError s!"closeNotify #{i} repeated a loss it had already reported: {msg}"

-- `setServerName` drives nothing, so `SSL_in_before` still reads true on a session teardown already
-- finished — it has to consult the session's own verdict instead. Accepting a name there would tell
-- the caller a peer identity had been configured for a handshake that can never run.
#eval do
  let clientCtx ← Context.Client.mk "" false
  let c ← Session.Client.mk clientCtx
  discard <| c.closeNotify

  match ← errorOf (c.setServerName "example.com") with
  | none => throw <| IO.userError "setServerName was accepted on a session already reported closed"
  | some msg =>
    unless (msg.splitOn "closed before it was negotiated").length > 1 do
      throw <| IO.userError s!"unexpected setServerName error: {msg}"

-- An address and a hostname are separate reference identities to OpenSSL, and before 3.5 setting
-- one left the other in place. A second `setServerName` must replace the first outright, or the
-- handshake is verified against a name the caller has withdrawn and fails on a valid certificate.
-- OpenSSL 3.5 and later clear both identities themselves, so this only bites on older builds.
#eval do
  let (certFile, keyFile) ← setupTestCerts
  let serverCtx ← Context.Server.mk certFile keyFile
  let caPEM ← IO.FS.readFile certFile
  let clientCtx ← Context.Client.mkFromPEM caPEM true

  let s ← Session.Server.mk serverCtx
  let c ← Session.Client.mk clientCtx

  -- The cert is for CN=localhost; the withdrawn IP must not still be checked against it.
  c.setServerName "192.0.2.1"
  c.setServerName "localhost"

  runHandshake c.toSession s.toSession
  assertEqN (← c.verifyResult) 0 "verifyResult after replacing an IP server name with a hostname"

-- A received fatal alert is queued as `SSL_AD_REASON_OFFSET` plus its descriptor, so the whole band
-- at and above that offset has to decode as an alert. `close_notify` is descriptor 0, which lands on
-- the offset exactly: sent at fatal level it is not absorbed as a clean shutdown, so it reaches the
-- error queue as reason 1000. An exclusive bound drops it through to the generic handshake message.
#eval do
  let clientCtx ← Context.Client.mk "" false
  let c ← Session.Client.mk clientCtx

  -- Drive the ClientHello out so the session is waiting on the server's flight.
  discard <| c.handshake
  discard <| c.drainEncrypted

  -- An unencrypted alert record: content type 21, TLS 1.2 record version, level 2 (fatal),
  -- description 0 (close_notify).
  let alert := ByteArray.mk #[0x15, 0x03, 0x03, 0x00, 0x02, 0x02, 0x00]
  discard <| c.feedEncrypted alert

  match ← errorOf c.handshake with
  | none => throw <| IO.userError "a fatal alert during the handshake was not reported"
  | some msg =>
    unless (msg.splitOn "fatal alert").length > 1 do
      throw <| IO.userError s!"a fatal-level close_notify was not decoded as an alert: {msg}"

-- `SSL_write` is refused once our own `close_notify` has gone out, but that closes only the write
-- direction: records the peer sent before it saw the alert are still decrypted and waiting. Treating
-- the refusal as fatal would finish the session and strand them.
#eval do
  let (certFile, keyFile) ← setupTestCerts
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false
  let s ← Session.Server.mk serverCtx
  let c ← Session.Client.mk clientCtx
  runHandshake c.toSession s.toSession

  let payload := "peer-record".toUTF8
  discard <| s.write payload
  discard <| c.closeNotify
  pipeEncrypted s.toSession c.toSession

  match ← errorOf (c.write "oops".toUTF8) with
  | none => throw <| IO.userError "a write after our own close_notify was accepted"
  | some msg =>
    unless (msg.splitOn "already shut down").length > 1 do
      throw <| IO.userError s!"write after close_notify reported the wrong condition: {msg}"

  match ← c.read? 1024 with
  | .data bytes => assertEqStr (String.fromUTF8! bytes) "peer-record"
  | _ => throw <| IO.userError "the peer's records were lost by a refused write"

-- A `write` refused after our own `close_notify` was never accepted, so there is no plaintext to
-- lose and the teardown that follows is a clean one. `write` queues the payload before offering it
-- to `SSL_write`, and the refusal leaves it there, so a session that reports the loss is reporting
-- bytes it declined to take -- out of the `closeNotify` a teardown path runs unconditionally.
#eval do
  let (certFile, keyFile) ← setupTestCerts
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false
  let s ← Session.Server.mk serverCtx
  let c ← Session.Client.mk clientCtx
  runHandshake c.toSession s.toSession

  discard <| c.closeNotify

  match ← errorOf (c.write "refused".toUTF8) with
  | none => throw <| IO.userError "a write after our own close_notify was accepted"
  | some msg =>
    unless (msg.splitOn "already shut down").length > 1 do
      throw <| IO.userError s!"write after close_notify reported the wrong condition: {msg}"

  match ← errorOf c.closeNotify with
  | none => pure ()
  | some msg =>
    throw <| IO.userError s!"closeNotify reported plaintext lost that write had refused: {msg}"

-- `feedEof` fixes the diagnosis of a session that never negotiated, so `closeNotify` and `read?` have
-- to agree on it whichever runs first. `SSL_shutdown` refuses to run in init and never reads, so the
-- shutdown path cannot get the verdict from OpenSSL the way the read path does.
#eval do
  let clientCtx ← Context.Client.mk "" false

  let readFirst ← do
    let c ← Session.Client.mk clientCtx
    discard <| c.handshake
    discard <| c.drainEncrypted
    c.feedEof
    errorOf (c.read? 1024)

  let closeFirst ← do
    let c ← Session.Client.mk clientCtx
    discard <| c.handshake
    discard <| c.drainEncrypted
    c.feedEof
    discard <| c.closeNotify
    errorOf (c.read? 1024)

  match readFirst, closeFirst with
  | some a, some b =>
    unless a == b do
      throw <| IO.userError s!"a truncated stream was classified by call order: '{a}' vs '{b}'"
  | _, _ => throw <| IO.userError "a truncated stream was not reported after feedEof"

-- A URI authority spells an IPv6 address `[::1]`. OpenSSL parses that form as neither an address nor
-- a hostname, so without stripping the brackets it goes out as SNI and binds the peer to a reference
-- name no certificate can carry. An address sends no SNI, so its ClientHello is shorter than a
-- hostname's by exactly the extension.
#eval do
  let clientCtx ← Context.Client.mk "" false

  let helloSize (host : String) : IO Nat := do
    let c ← Session.Client.mk clientCtx
    c.setServerName host
    discard <| c.handshake
    return (← c.drainEncrypted).size

  let bare ← helloSize "::1"
  let bracketed ← helloSize "[::1]"
  let named ← helloSize "abcde"

  unless bare == bracketed do
    throw <| IO.userError s!"[::1] was not treated as an address: ClientHello {bracketed} vs {bare}"
  unless named > bare do
    throw <| IO.userError s!"a hostname did not add an SNI extension: {named} vs {bare}"

-- A trailing dot spells an absolute FQDN. RFC 6066 §3 forbids one in the SNI `HostName`, and
-- OpenSSL neither rejects it nor strips it before matching, so leaving it on would put a
-- non-conforming name on the wire and then fail verification against every certificate.
#eval do
  let clientCtx ← Context.Client.mk "" false

  let helloSize (host : String) : IO Nat := do
    let c ← Session.Client.mk clientCtx
    c.setServerName host
    discard <| c.handshake
    return (← c.drainEncrypted).size

  let absolute ← helloSize "localhost."
  let relative ← helloSize "localhost"

  unless absolute == relative do
    throw <| IO.userError
      s!"a trailing dot reached the SNI extension: ClientHello {absolute} vs {relative}"

-- The stripped dot must leave the hostname bound for verification too, not just shorten the SNI.
#eval do
  let (certFile, keyFile) ← setupTestCerts
  let serverCtx ← Context.Server.mk certFile keyFile
  let caPEM ← IO.FS.readFile certFile
  let clientCtx ← Context.Client.mkFromPEM caPEM true

  let s ← Session.Server.mk serverCtx
  let c ← Session.Client.mk clientCtx

  -- The certificate is for CN=localhost, which only matches once the trailing dot is gone.
  c.setServerName "localhost."

  runHandshake c.toSession s.toSession
  assertEqN (← c.verifyResult) 0 "verifyResult for an absolute FQDN server name"

-- A bare `"."` is the root, which strips to nothing. It has to be refused as an empty name rather
-- than reaching `SSL_set1_host`, which answers success for one and verifies against nothing.
#eval do
  let clientCtx ← Context.Client.mk "" false
  let c ← Session.Client.mk clientCtx

  match ← errorOf (c.setServerName ".") with
  | none => throw <| IO.userError "a bare '.' server name was accepted"
  | some msg =>
    unless (msg.splitOn "the server name is empty").length > 1 do
      throw <| IO.userError s!"unexpected '.' server name error: {msg}"

-- A URI authority reserves the bracketed form for an address, so a bracketed name that is not one is
-- malformed. Accepting it would put the brackets on the wire as SNI and bind the peer to a name no
-- certificate can carry, surfacing a round trip later as a certificate mismatch. A scope id is the
-- realistic way to get here: `a2i_IPADDRESS` does not accept one, so `[fe80::1%25eth0]` — a
-- well-formed RFC 6874 authority — falls out of the address branch.
#eval do
  let clientCtx ← Context.Client.mk "" false

  for host in ["[a]", "[]", "[::1", "[fe80::1%25eth0]"] do
    let c ← Session.Client.mk clientCtx
    match ← errorOf (c.setServerName host) with
    | none => throw <| IO.userError s!"the bracketed server name {host} was accepted"
    | some msg =>
      unless (msg.splitOn "not a valid IP address").length > 1 do
        throw <| IO.userError s!"unexpected error for {host}: {msg}"

  -- The bracketed forms that do parse as an address stay accepted, trailing dot and all.
  for host in ["[::1]", "[::1].", "[1.2.3.4]"] do
    let c ← Session.Client.mk clientCtx
    match ← errorOf (c.setServerName host) with
    | none => pure ()
    | some msg => throw <| IO.userError s!"the bracketed address {host} was rejected: {msg}"

-- A TLS 1.2 `ServerHello` followed by a `Certificate` whose DER cannot be parsed. The handshake
-- fails inside the certificate parser, so it never gets far enough to need a `ServerKeyExchange`.
def tls12BadCertificateFlight : ByteArray :=
  let serverHello : Array UInt8 :=
    #[0x03, 0x03] ++                                              -- legacy_version: TLS 1.2
    (Array.range 32).map (fun i => (0x41 + i % 26).toUInt8) ++     -- random
    #[0x00] ++                                                    -- empty session id
    #[0xC0, 0x2F] ++                                              -- ECDHE-RSA-AES128-GCM-SHA256
    #[0x00] ++                                                    -- null compression
    #[0x00, 0x05, 0xFF, 0x01, 0x00, 0x01, 0x00]                   -- renegotiation_info
  let certificate : Array UInt8 :=
    #[0x00, 0x00, 0x2B] ++                                        -- certificate_list length
    #[0x00, 0x00, 0x28] ++                                        -- certificate length
    Array.replicate 40 (0xA5 : UInt8)                             -- not DER
  ByteArray.mk (record (handshake 0x02 serverHello) ++ record (handshake 0x0B certificate))
where
  handshake (ty : UInt8) (body : Array UInt8) : Array UInt8 :=
    #[ty, (body.size / 65536).toUInt8, (body.size / 256 % 256).toUInt8, (body.size % 256).toUInt8]
      ++ body
  record (body : Array UInt8) : Array UInt8 :=
    #[0x16, 0x03, 0x03, (body.size / 256).toUInt8, (body.size % 256).toUInt8] ++ body

-- OpenSSL raises its library-wide `ERR_R_*` conditions under `ERR_LIB_SSL` for failures of its own,
-- and `ERR_GET_REASON` leaves the reason flags on those codes, which lifts them clear of every
-- `SSL_R_*` and into the band that decodes a received alert. A peer certificate that cannot be
-- parsed arrives exactly that way, so blaming the peer for it would report a local parse failure as
-- the peer's verdict on us.
#eval do
  let clientCtx ← Context.Client.mk "" false
  let c ← Session.Client.mk clientCtx

  discard <| c.handshake
  discard <| c.drainEncrypted
  discard <| c.feedEncrypted tls12BadCertificateFlight

  match ← errorOf c.handshake with
  | none => throw <| IO.userError "an unparseable peer certificate must fail the handshake"
  | some msg =>
    if (msg.splitOn "fatal alert").length > 1 then
      throw <| IO.userError s!"a local certificate-parse failure was blamed on the peer: {msg}"
    unless (msg.splitOn "the TLS handshake failed").length > 1 do
      throw <| IO.userError s!"unexpected unparseable-certificate error: {msg}"
