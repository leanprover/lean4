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
-- Test: a close_notify arriving behind unread application data.
-- ---------------------------------------------------------------------------

-- A peer may send its last application record and its `close_notify` in a single flight, so both
-- land in the input BIO together. Starting our own shutdown at that point must neither consume nor
-- reject the record: `closeNotify` reports want-read while plaintext is still undelivered, `read?`
-- hands the record out and only then reports `.closed`, and the shutdown completes afterwards.
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

  -- Initiating our side of the shutdown must not consume or reject the unread
  -- application record that precedes the peer's close_notify.
  let clientClosing ← clientSess.closeNotify
  match clientClosing with
  | some .read => pure ()
  | some .write => throw <| IO.userError "client closeNotify should await peer input"
  | none => throw <| IO.userError "client closeNotify completed with unread application data"

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
-- `close_notify` to finish on. `closeNotify` must send our alert, report want-read, and keep the
-- plaintext intact for as many calls as it takes — a session with undelivered data must survive an
-- early shutdown rather than fail.
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
    | some .read => pure ()
    | some .write => throw <| IO.userError s!"closeNotify {attempt} should await peer input"
    | none => throw <| IO.userError s!"closeNotify {attempt} completed with plaintext still unread"

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

-- Once a fatal alert has torn the session down, OpenSSL answers every further operation with a bare
-- `SSL_ERROR_SYSCALL`. Both BIOs are memory BIOs, so that is never a transport EOF, and an aborted
-- session must not be reported as `end of file` — a caller would read that as a clean end of stream.
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
-- is refused rather than allowed to buffer without limit. The first write is always admitted: by
-- then `SSL_write` has taken the payload and requires the same bytes back on retry.
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
