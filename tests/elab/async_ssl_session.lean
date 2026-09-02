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

-- ---------------------------------------------------------------------------
-- Assertions
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

/-- Runs `act` and returns the raised `IO` exception's message, or `none` if it succeeded. -/
def errorOf (act : IO α) : IO (Option String) := do
  try
    discard act; return none
  catch e =>
    return some (toString e)

/-- Asserts that `act` raises, and that the message names `needle`. -/
def assertRaises (needle label : String) (act : IO α) : IO Unit := do
  match ← errorOf act with
  | none => throw <| IO.userError s!"{label}: expected a raise naming '{needle}'"
  | some msg =>
    unless (msg.splitOn needle).length > 1 do
      throw <| IO.userError s!"{label}: expected '{needle}', got '{msg}'"

/-- Asserts that `act` raises, but with a message that does *not* name `needle`. -/
def assertRaisesWithout (needle label : String) (act : IO α) : IO Unit := do
  match ← errorOf act with
  | none => throw <| IO.userError s!"{label}: expected a raise"
  | some msg =>
    if (msg.splitOn needle).length > 1 then
      throw <| IO.userError s!"{label}: reported '{needle}': {msg}"

/-- Asserts that `act` completes without raising. -/
def assertOk (label : String) (act : IO α) : IO Unit := do
  match ← errorOf act with
  | none => pure ()
  | some msg => throw <| IO.userError s!"{label} raised: {msg}"

/--
Asserts that a shutdown step reports nothing left to do. `closeNotify` returning `none` rather than
`true` is what makes a teardown loop terminate, so the value has to be checked, not just the absence
of a raise.
-/
def assertDone (label : String) (act : IO Bool) : IO Unit := do
  unless ← act do
    throw <| IO.userError s!"{label}: expected true, got false"

/-- Asserts that a shutdown step is still waiting on encrypted input from the peer. -/
def assertWantRead (label : String) (act : IO Bool) : IO Unit := do
  if ← act then
    throw <| IO.userError s!"{label}: expected false, got true"

-- ---------------------------------------------------------------------------
-- Fixtures
-- ---------------------------------------------------------------------------

def testCertPEM : String := include_cert% "async_ssl_certs/multisan.pem"

def testKeyPEM : String := include_cert% "async_ssl_certs/key.pem"

/--
A `dNSName` the test certificate carries. The `Context` layer sets
`X509_CHECK_FLAG_NEVER_CHECK_SUBJECT`, so only a SAN can satisfy hostname verification — a
certificate naming the host in its CN alone never matches.
-/
def testHost : String := "alpha.test.local"

/-- The PEM travels as text, so no test needs the filesystem. -/
def serverCtx : IO Context.Server :=
  Context.Server.mk { cert := .text testCertPEM, key := .text testKeyPEM }

/-- A client that does not verify the peer, for the tests that are not about identity. -/
def clientCtx : IO Context.Client := Context.Client.mk { verifyPeer := false }

/-- A client that trusts the test certificate as an anchor and verifies the peer against it. -/
def verifyingClientCtx : IO Context.Client :=
  Context.Client.mk { ca := some (.text testCertPEM), verifyPeer := true }

def handshakeStep (c : Session cr) (s : Session sr) : IO (Bool × Bool) := do
  let cd ← c.handshake
  let cOut ← c.drainEncrypted
  if cOut.size > 0 then
    discard <| s.feedEncrypted cOut
  let sd ← s.handshake
  let sOut ← s.drainEncrypted
  if sOut.size > 0 then
    discard <| c.feedEncrypted sOut
  return (cd, sd)

/-- `fuel` bounds the loop so a regression that stops the handshake converging fails rather than hangs. -/
def runHandshake (c : Session cr) (s : Session sr) (fuel : Nat := 32) : IO Unit := do
  match fuel with
  | 0 => throw <| IO.userError "the handshake did not converge"
  | fuel' + 1 =>
    let (cd, sd) ← handshakeStep c s
    unless cd && sd do runHandshake c s fuel'

def pipeEncrypted (src : Session a) (dst : Session b) : IO Unit := do
  let bytes ← src.drainEncrypted
  if bytes.size > 0 then
    discard <| dst.feedEncrypted bytes

/-- A fresh client session on a non-verifying context, for the tests that need no peer. -/
def mkClient (host : Option String := none) : IO Session.Client := do
  Session.Client.mk (← clientCtx) host

/-- A fresh client/server pair, before the handshake. -/
def mkPair : IO (Session.Client × Session.Server) := do
  return (← mkClient, ← Session.Server.mk (← serverCtx))

/-- A client/server pair with the handshake already complete. -/
def mkHandshakenPair : IO (Session.Client × Session.Server) := do
  let (c, s) ← mkPair
  runHandshake c s
  return (c, s)

/-- A client/server pair whose client verifies the peer against the test certificate. -/
def mkVerifyingPair (host : Option String := none) : IO (Session.Client × Session.Server) := do
  return (← Session.Client.mk (← verifyingClientCtx) host, ← Session.Server.mk (← serverCtx))

/-- Reads every plaintext byte the session can produce without further input. -/
def drainPlaintext (s : Session role) : IO ByteArray := do
  let mut acc := ByteArray.empty
  let mut go := true
  while go do
    match ← s.read 1000000 with
    | .data b => acc := acc ++ b
    | _ => go := false
  return acc

-- ---------------------------------------------------------------------------
-- Test: a verifying client accepts a certificate that names the host it asked for.
-- ---------------------------------------------------------------------------

def testVerifyingHandshake : IO Unit := do
  -- The host is bound at construction, which is the path a caller is meant to take.
  let (c, s) ← mkVerifyingPair (some testHost)

  runHandshake c s

  assertEqN (← c.verifyResult) 0 "verifyResult after a verifying handshake"
  assertEqStr (← c.verifyResultString) "ok"

def testInProcessHandshake : IO Unit := do
  let c ← mkClient (some testHost)
  let s ← Session.Server.mk (← serverCtx)
  runHandshake c s
  discard <| c.verifyResult

-- ---------------------------------------------------------------------------
-- Test: write / pendingEncrypted / drainEncrypted / feedEncrypted / read
-- ---------------------------------------------------------------------------

def testDataTransfer : IO Unit := do
  let (c, s) ← mkHandshakenPair

  -- write plaintext → encrypted bytes appear in the write BIO.
  let msg := "hello, tls!".toUTF8
  discard <| c.write msg

  -- pendingEncrypted > 0 before draining.
  assertGt (← c.pendingEncrypted) 0 "pendingEncrypted"

  -- Pipe to server and read back.
  pipeEncrypted c s
  match ← s.read 1024 with
  | .data bytes => assertEqStr (String.fromUTF8! bytes) "hello, tls!"
  | _ => throw <| IO.userError "expected data from server session"

  -- After draining, pendingEncrypted drops to 0.
  assertEqN (← c.pendingEncrypted) 0 "pendingEncrypted after drain"

  -- read reports wantRead when no data is available.
  match ← c.read 1024 with
  | .wantRead => return ()
  | _ => throw <| IO.userError "expected wantRead when no data available"

-- ---------------------------------------------------------------------------
-- Test: pendingPlaintext — write 100 bytes, read 10, rest stays buffered.
-- ---------------------------------------------------------------------------

def testPendingPlaintext : IO Unit := do
  let (c, s) ← mkHandshakenPair

  let bigMsg := (String.ofList (List.replicate 100 'x')).toUTF8
  discard <| c.write bigMsg
  pipeEncrypted c s

  -- Read only 10 bytes; the remaining 90 stay in SSL's plaintext buffer.
  discard <| s.read 10
  assertEqN (← s.pendingPlaintext) 90 "pendingPlaintext after partial read"

-- ---------------------------------------------------------------------------
-- Test: empty write returns none.
-- ---------------------------------------------------------------------------

def testEmptyWrite : IO Unit := do
  let (c, _) ← mkHandshakenPair
  unless ← c.write ByteArray.empty do
    throw <| IO.userError "empty write should return none"

-- ---------------------------------------------------------------------------
-- Test: peek returns wantRead (not .data empty) when no data is buffered.
-- ---------------------------------------------------------------------------

def testReadZero : IO Unit := do
  let (_, s) ← mkHandshakenPair

  -- No data has been sent; peek must signal wantRead, not return .data empty.
  match ← s.peek with
  | .wantRead => return ()
  | .data b   => throw <| IO.userError s!"peek returned .data (size={b.size}) instead of wantRead"
  | .closed   => throw <| IO.userError "peek returned .closed unexpectedly"

-- ---------------------------------------------------------------------------
-- Test: queued writes reach the peer in the order they were made.
-- ---------------------------------------------------------------------------

-- Memory BIOs are always writable, so a post-handshake `SSL_write` never blocks and never queues.
-- Writing before the handshake is what fills `pending_writes`, making this an ordering test of the
-- queue rather than of TLS record delivery.
def testPendingWriteOrder : IO Unit := do
  let (c, s) ← mkPair

  let msgs := #["first", "second", "third"]
  for m in msgs do
    match ← c.write m.toUTF8 with
    | false => pure ()
    | true => throw <| IO.userError s!"'{m}' was taken immediately, so the queue is left untested"

  runHandshake c s

  -- The empty write flushes the whole queue; the peer must see one stream in the original order.
  unless ← c.write ByteArray.empty do
    throw <| IO.userError "the queued plaintext did not flush after the handshake"
  pipeEncrypted c s

  let expected := String.join msgs.toList
  let received := String.fromUTF8! (← drainPlaintext s)
  unless received == expected do
    throw <| IO.userError s!"write order mismatch: expected '{expected}', got '{received}'"

-- ---------------------------------------------------------------------------
-- Test: verifyResultString names the verdict, and distinguishes the two outcomes.
-- ---------------------------------------------------------------------------

def testVerifyResultString : IO Unit := do
  -- A verification that passed and one that failed have to read differently, or the accessor
  -- carries no information at all.
  let (ok, okPeer) ← mkVerifyingPair
  ok.setServerName testHost
  runHandshake ok okPeer
  assertEqStr (← ok.verifyResultString) "ok"

  let (bad, badPeer) ← mkVerifyingPair
  bad.setServerName "wrong.example.com"
  discard <| errorOf (runHandshake bad badPeer)

  if (← bad.verifyResultString) == "ok" then
    throw <| IO.userError "verifyResultString reported 'ok' for a failed verification"
  assertGt (← bad.verifyResult) 0 "verifyResult after a failed verification"

  -- `verifyPeer := false` does not stop the chain being checked, only the handshake being failed
  -- by it, so the accessor still reports the verdict rather than a blanket `ok`. Reading a `0`
  -- here as "the peer is authenticated" would be wrong twice over.
  let (unverified, _) ← mkHandshakenPair
  assertEqStr (← unverified.verifyResultString) "self-signed certificate"

-- ---------------------------------------------------------------------------
-- Test: peerName answers the question verifyResult cannot.
-- ---------------------------------------------------------------------------

def testPeerName : IO Unit := do
  -- Bound to a name the certificate carries: authenticated, and the matched name says which.
  let (c, s) ← mkVerifyingPair (some testHost)
  runHandshake c s
  assertEqN (← c.verifyResult) 0 "a verifying handshake reports ok"
  match ← c.peerName with
  | some name => assertEqStr name testHost
  | none => throw <| IO.userError "peerName reported no matched identity for a verified peer"

  -- Bound to nothing: the chain is still validated and `verifyResult` still answers `0`, but no
  -- certificate was ever tied to this peer. That difference is only visible through `peerName`.
  let (anon, anonPeer) ← mkVerifyingPair
  runHandshake anon anonPeer
  assertEqN (← anon.verifyResult) 0 "an identity-less handshake still reports ok"
  match ← anon.peerName with
  | none => pure ()
  | some name =>
    throw <| IO.userError s!"peerName named '{name}' for a session bound to no identity"

-- ---------------------------------------------------------------------------
-- Test: negotiatedVersion reports a modern TLS version after handshake.
-- ---------------------------------------------------------------------------

def testNegotiatedVersion : IO Unit := do
  let (c, s) ← mkHandshakenPair

  -- The Context layer pins a TLS 1.2 minimum, so both ends must negotiate TLSv1.2 or 1.3.
  let v ← c.negotiatedVersion
  unless v == "TLSv1.3" || v == "TLSv1.2" do
    throw <| IO.userError s!"unexpected negotiated version '{v}'"
  -- Both peers must agree on the negotiated version.
  assertEqStr (← s.negotiatedVersion) v

-- ---------------------------------------------------------------------------
-- Test: a full bidirectional close_notify exchange completes on both ends.
-- ---------------------------------------------------------------------------

-- Drive the close_notify exchange to completion, piping each side's alert to the
-- other. `fuel` bounds the loop so a regression cannot hang the test.
partial def runShutdown (fuel : Nat) (a : Session ar) (b : Session br) : IO Unit := do
  if fuel == 0 then
    throw <| IO.userError "close_notify exchange did not converge"
  let ra ← a.closeNotify
  pipeEncrypted a b
  let rb ← b.closeNotify
  pipeEncrypted b a
  unless ra && rb do runShutdown (fuel - 1) a b

def testCloseNotify : IO Unit := do
  let (c, s) ← mkHandshakenPair

  -- A fresh client shutdown sends its close_notify but still awaits the peer's.
  match ← c.closeNotify with
  | false => pure ()
  | true => throw <| IO.userError "initial closeNotify completed before the peer responded"

  -- Pipe the alert across and run both sides to a clean bidirectional shutdown.
  pipeEncrypted c s
  runShutdown 16 s c

  -- After a clean shutdown, both report completion.
  unless (← c.closeNotify) && (← s.closeNotify) do
    throw <| IO.userError "closeNotify did not report a completed shutdown"

-- ---------------------------------------------------------------------------
-- Test: a close_notify arriving behind unread application data.
-- ---------------------------------------------------------------------------

-- A peer may send its last application record and its `close_notify` in a single flight, so both
-- land in the input BIO together. Starting our own shutdown at that point must neither consume nor
-- reject the record: `closeNotify` reports `none` — our alert is out and the peer's sits behind
-- plaintext that no socket I/O can carry us past — `read` hands the record out and only then
-- reports `.closed`, and a further `closeNotify` completes the shutdown.
--
-- OpenSSL rejects an application record read *inside* `SSL_shutdown` as a fatal protocol error
-- (`application data after close notify`), so the runtime peeks before letting the shutdown read.

def testCloseNotifyWithPendingData : IO Unit := do
  let (c, s) ← mkHandshakenPair

  -- Deliver a final application record and the server's close_notify together.
  discard <| s.write "final".toUTF8
  match ← s.closeNotify with
  | false => pure ()
  | true => throw <| IO.userError "server closeNotify completed before the peer responded"
  pipeEncrypted s c

  -- Initiating our side of the shutdown must not consume or reject the unread application record
  -- that precedes the peer's close_notify. The alert is already buffered behind that record, so no
  -- socket input is outstanding and asking for some would strand a caller that loops on this alone.
  assertDone "client closeNotify asked for input that had already arrived" c.closeNotify

  match ← c.read 1024 with
  | .data bytes => assertEqStr (String.fromUTF8! bytes) "final"
  | .wantRead => throw <| IO.userError "expected final application data before close_notify"
  | .closed => throw <| IO.userError "close_notify was reported before final application data"

  match ← c.read 1024 with
  | .closed => pure ()
  | .data _ => throw <| IO.userError "unexpected application data after final record"
  | .wantRead => throw <| IO.userError "expected buffered close_notify after final record"

  -- Nothing is left undelivered, so the client's shutdown now completes.
  unless ← c.closeNotify do
    throw <| IO.userError "client shutdown did not complete after the peer's close_notify was read"

  pipeEncrypted c s
  unless ← s.closeNotify do
    throw <| IO.userError "server shutdown did not complete after receiving close_notify"

-- ---------------------------------------------------------------------------
-- Test: closing while the peer's plaintext is unread and its alert has not arrived.
-- ---------------------------------------------------------------------------

-- The same shutdown-before-drain race, but the peer has only sent data so far: there is no buffered
-- `close_notify` to finish on. `closeNotify` must send our alert and keep the plaintext intact for
-- as many calls as it takes — a session with undelivered data must survive an early shutdown rather
-- than fail, and must never ask for input that cannot advance it.
def testCloseNotifyBeforeDrainingData : IO Unit := do
  let (c, s) ← mkHandshakenPair

  discard <| s.write "final".toUTF8
  pipeEncrypted s c

  for attempt in [1, 2] do
    assertDone s!"closeNotify {attempt} asked for input it could not use" c.closeNotify

  match ← c.read 1024 with
  | .data bytes => assertEqStr (String.fromUTF8! bytes) "final"
  | .wantRead => throw <| IO.userError "unread plaintext was consumed by closeNotify"
  | .closed => throw <| IO.userError "session reported closed with plaintext still unread"

  -- The peer answers our alert; both ends then reach a clean shutdown.
  pipeEncrypted c s
  unless ← s.closeNotify do
    throw <| IO.userError "server shutdown did not complete after receiving close_notify"

  pipeEncrypted s c
  unless ← c.closeNotify do
    throw <| IO.userError "client shutdown did not complete after receiving close_notify"

-- ---------------------------------------------------------------------------
-- Test: plaintext written before the handshake completes is queued and replayed.
-- ---------------------------------------------------------------------------

-- Calling `write` before the handshake forces SSL_write to drive the handshake, which blocks on
-- WANT_READ. The plaintext must be queued (not dropped, not failed) and delivered once the
-- handshake finishes — exercising the `pending_writes` blocked/flush path that is otherwise hard to
-- reach with always-writable memory BIOs.
def testWriteBeforeHandshake : IO Unit := do
  let (c, s) ← mkPair

  -- Write before handshaking: the data is queued, and OpenSSL asks for socket input.
  match ← c.write "early".toUTF8 with
  | false => pure ()
  | true => throw <| IO.userError "write before handshake should not complete immediately"

  -- Complete the handshake; the queued plaintext stays pending throughout.
  runHandshake c s

  -- An empty write now flushes the queued plaintext into encrypted output.
  unless ← c.write ByteArray.empty do
    throw <| IO.userError "queued plaintext should flush cleanly after the handshake"

  pipeEncrypted c s
  match ← s.read 1024 with
  | .data b => assertEqStr (String.fromUTF8! b) "early"
  | _ => throw <| IO.userError "queued plaintext was not delivered after the handshake"

-- ---------------------------------------------------------------------------
-- Test: `read` reports that it is waiting on the peer, in both the read and peek paths.
-- ---------------------------------------------------------------------------

-- A session with an empty input BIO is waiting on the peer, and both the sized read and the peek
-- have to say so. `ReadResult.wantRead` and `.closed` are both nullary, so they are boxed
-- constructor indices on the C side rather than allocations -- easy to get one off by one.
def testReadWantRead : IO Unit := do
  let (c, s) ← mkPair

  let expectWantRead (r : ReadResult) (label : String) : IO Unit :=
    match r with
    | .wantRead => pure ()
    | .data b => throw <| IO.userError s!"{label}: expected wantRead, got data ({b.size} bytes)"
    | .closed => throw <| IO.userError s!"{label}: expected wantRead, got closed"

  -- Before the handshake, and again after the ClientHello has been drained, the session is waiting
  -- on encrypted input in both the peek and the sized-read paths.
  expectWantRead (← c.peek) "peek before handshake"
  expectWantRead (← c.read 1024) "read before handshake"
  let hello ← c.drainEncrypted
  expectWantRead (← c.peek) "peek after draining ClientHello"
  expectWantRead (← c.read 1024) "read after draining ClientHello"

  -- Once the handshake is done and no plaintext is buffered, it is still input we are waiting for.
  discard <| s.feedEncrypted hello
  runHandshake c s
  expectWantRead (← c.peek) "peek after handshake"
  expectWantRead (← c.read 1024) "read after handshake"
  expectWantRead (← s.read 1024) "server read after handshake"

-- ---------------------------------------------------------------------------
-- Run the named tests
-- ---------------------------------------------------------------------------

#eval do
  testVerifyingHandshake
  testReadWantRead
  testInProcessHandshake
  testDataTransfer
  testPendingPlaintext
  testEmptyWrite
  testReadZero
  testPendingWriteOrder
  testVerifyResultString
  testPeerName
  testNegotiatedVersion
  testCloseNotify
  testCloseNotifyWithPendingData
  testCloseNotifyBeforeDrainingData
  testWriteBeforeHandshake

-- ---------------------------------------------------------------------------
-- Regression tests
-- ---------------------------------------------------------------------------

/-- A record OpenSSL rejects as fatally malformed on an established session. -/
def corruptRecord : ByteArray := ByteArray.mk (List.replicate 64 (0x17 : UInt8)).toArray

-- A client that verifies the peer and pins the server's certificate as its CA must still reject the
-- handshake when the requested SNI host does not match the certificate's SANs. This proves
-- `setServerName` wires up hostname verification (SSL_set1_host), not just SNI.
#eval do
  let (c, s) ← mkVerifyingPair
  c.setServerName "wrong.example.com"

  assertRaises "certificate could not be verified" "a handshake against a mismatched host"
    (runHandshake c s)

#eval do
  -- A corrupt encrypted record fed into the server's input BIO. The record is fatal, so each path
  -- needs its own session: the torn-down one refuses further input.
  let corrupted : IO Session.Server := do
    let (_, s) ← mkHandshakenPair
    discard <| s.feedEncrypted corruptRecord
    return s

  -- The sized read and the peek must both raise, not silently return `.wantRead`.
  assertRaises "unrecognized version" "read 1 on a corrupt record" ((← corrupted).read 1)
  assertRaises "unrecognized version" "peek on a corrupt record" (← corrupted).peek

-- A `read` larger than one TLS record returns at most one record (16 KiB) per call, and successive
-- calls return the rest with no data loss (regression for the `read` allocation cap).
#eval do
  let (c, s) ← mkHandshakenPair

  let payload := ByteArray.mk ((List.replicate 100000 (0x41 : UInt8)).toArray)
  discard <| c.write payload
  pipeEncrypted c s

  -- One oversized read returns exactly one record's worth of plaintext.
  let first ← s.read 1000000
  let firstSize := match first with | .data b => b.size | _ => 0
  assertEqN firstSize.toUInt64 16384 "first oversized read returns one record"

  -- Drain the rest; the total must equal what was written (no data lost to the cap).
  let rest ← drainPlaintext s
  assertEqN (firstSize + rest.size).toUInt64 100000 "total plaintext received"

-- When plaintext is already buffered (a partial read left a remainder), a subsequent oversized
-- `read` returns exactly the buffered remainder rather than a full record.
#eval do
  let (c, s) ← mkHandshakenPair

  -- One record's worth of plaintext, sent and decrypted via a partial read.
  discard <| c.write "HELLO".toUTF8
  pipeEncrypted c s

  -- Read only the first 2 bytes; the remaining 3 stay buffered (SSL_pending == 3).
  let part ← s.read 2
  assertEqN (match part with | .data b => b.size.toUInt64 | _ => 0) 2 "partial read size"
  assertEqN (← s.pendingPlaintext) 3 "buffered remainder after partial read"

  -- An oversized read now returns exactly the 3 buffered bytes.
  let rest ← s.read 1000000
  assertEqN (match rest with | .data b => b.size.toUInt64 | _ => 0) 3 "oversized read returns buffered remainder"

-- `peek` reports that plaintext is available *without consuming any of it*. Every other peek in this
-- file is a want-or-raise case, so nothing there would notice `SSL_peek` silently becoming
-- `SSL_read` -- which is the whole of what `peek` promises.
#eval do
  let (c, s) ← mkHandshakenPair

  discard <| c.write "peekable".toUTF8
  pipeEncrypted c s

  match ← s.peek with
  | .data b => assertEqN b.size.toUInt64 0 "a peek reports availability as an empty ByteArray"
  | .wantRead => throw <| IO.userError "peek reported wantRead with plaintext already buffered"
  | .closed => throw <| IO.userError "peek reported closed with plaintext already buffered"

  -- Nothing was consumed, so the record is still whole and a real read returns every byte of it.
  assertEqN (← s.pendingPlaintext) 8 "a peek leaves pendingPlaintext untouched"

  match ← s.read 1024 with
  | .data b => assertEqStr (String.fromUTF8! b) "peekable"
  | _ => throw <| IO.userError "the peeked plaintext was consumed by the peek"

-- `feedEncrypted` takes all of `data` or raises, so a caller never has a partial feed to resume
-- from. What is observable is that nothing is dropped: every fed byte turns up as plaintext, and an
-- empty feed is a no-op rather than an error.
#eval do
  let (c, s) ← mkHandshakenPair

  discard <| c.write "counted".toUTF8
  let encrypted ← c.drainEncrypted
  assertGt encrypted.size.toUInt64 0 "the write produced ciphertext to feed"

  assertOk "an empty feed is a no-op" (s.feedEncrypted ByteArray.empty)
  s.feedEncrypted encrypted
  assertEqN (← s.pendingEncryptedInput) encrypted.size.toUInt64 "feedEncrypted took all of data"

  match ← s.read 1024 with
  | .data b => assertEqStr (String.fromUTF8! b) "counted"
  | _ => throw <| IO.userError "the fed ciphertext did not turn up as plaintext"

  assertEqN (← s.pendingEncryptedInput) 0 "the whole record was consumed"

-- `closeNotify` owns the pending-write queue: plaintext `write` accepted must reach the peer before
-- the alert that ends the session, with no explicit flush from the caller. A write issued before the
-- handshake blocks on WANT_READ, which is the only way to get plaintext queued behind memory BIOs.
#eval do
  let (c, s) ← mkPair

  discard <| c.write "queued-payload".toUTF8
  runHandshake c s

  -- No explicit `write ByteArray.empty` flush: `closeNotify` is responsible for the queue.
  discard <| c.closeNotify
  pipeEncrypted c s

  match ← s.read 1024 with
  | .data b => assertEqStr (String.fromUTF8! b) "queued-payload"
  | .closed => throw <| IO.userError "closeNotify dropped the plaintext queued by write"
  | .wantRead => throw <| IO.userError "expected the queued plaintext, got wantRead"

-- Once a record has been rejected as fatally malformed, OpenSSL answers every further operation with
-- a bare `SSL_ERROR_SYSCALL` — no alert is involved, the session is torn down locally. Both BIOs are
-- memory BIOs, so that is never a transport EOF, and an aborted session must not be reported as
-- `end of file` — a caller would read that as a clean end of stream.
#eval do
  let (_, s) ← mkHandshakenPair

  discard <| s.feedEncrypted corruptRecord
  assertRaises "unrecognized version" "the first read of a corrupt record" (s.read 128)

  assertRaisesWithout "end of file" "read after a fatal error" (s.read 128)
  assertRaisesWithout "end of file" "write after a fatal error" (s.write "x".toUTF8)
  assertRaisesWithout "end of file" "handshake after a fatal error" s.handshake

-- `read` and `handshake` short-circuit on the recorded failure and never touch the input BIO again,
-- so bytes fed to an aborted session are never consumed. Reporting success for them would let a
-- transport pump grow the BIO without bound while the caller is told the data was accepted.
#eval do
  let (_, s) ← mkHandshakenPair

  discard <| s.feedEncrypted corruptRecord
  discard <| errorOf (s.read 128)

  let chunk := ByteArray.mk (List.replicate 1024 (0x58 : UInt8)).toArray
  for i in [0, 1, 2] do
    assertRaisesWithout "end of file" s!"feedEncrypted #{i} on an aborted session"
      (s.feedEncrypted chunk)

-- The same holds once the peer has closed cleanly: OpenSSL short-circuits every read on a session
-- that has seen `close_notify`, so bytes fed after it are never consumed either. A transport pump
-- that keeps feeding a half-closed socket would otherwise grow the input BIO without bound while
-- being told the data was taken.
#eval do
  let (c, s) ← mkHandshakenPair
  discard <| s.closeNotify
  pipeEncrypted s c

  match ← c.read 1024 with
  | .closed => pure ()
  | .data b => throw <| IO.userError s!"expected the peer's close_notify, got data ({b.size} bytes)"
  | .wantRead => throw <| IO.userError "expected the peer's close_notify, got wantRead"

  let chunk := ByteArray.mk (List.replicate 1024 (0x58 : UInt8)).toArray
  for i in [0, 1, 2] do
    assertRaises "the peer already closed" s!"feedEncrypted #{i} after the peer's close_notify"
      (c.feedEncrypted chunk)

-- Plaintext HTTP reaching a TLS port is the most common way a server meets a peer that is not
-- speaking TLS, and OpenSSL diagnoses it specifically rather than as a bad record version. Naming it
-- is what distinguishes a misdirected client from a genuine handshake failure.
#eval do
  let s ← Session.Server.mk (← serverCtx)

  discard <| s.feedEncrypted "GET / HTTP/1.1\r\nHost: example.com\r\n\r\n".toUTF8
  assertRaises "plaintext HTTP request" "an HTTP request to a TLS server" s.handshake

-- SNI and the hostname check both travel with the handshake, so setting a server name afterwards
-- cannot take effect and must be rejected instead of silently succeeding.
#eval do
  let (c, _) ← mkHandshakenPair
  assertRaises "before the handshake" "setServerName after the handshake"
    (c.setServerName "evil.example.com")

-- A session that never handshaked has nothing to close, so teardown must not raise. Repeated calls
-- stay a no-op.
#eval do
  let c ← mkClient
  for i in [0, 1, 2] do
    assertDone s!"closeNotify #{i} on a fresh session" c.closeNotify

-- Reporting a clean close has to end the session: a fatal error also puts one back in init, so the
-- branch that reports "nothing to tear down" cannot leave it looking ready to negotiate.
--
-- The session is finished, but nothing fatal ever happened to it: reporting one would send a caller
-- hunting for a protocol failure that only its own teardown caused.
#eval do
  let c ← mkClient
  discard <| c.closeNotify

  let closed := "closed before it was negotiated"
  assertRaises closed "handshake after closeNotify" c.handshake
  assertRaises closed "write after closeNotify" (c.write "x".toUTF8)
  assertRaises closed "read after closeNotify" (c.read 128)
  assertRaises closed "feedEncrypted after closeNotify" (c.feedEncrypted "x".toUTF8)

-- The same holds once a fatal error has torn the session down: the shutdown has nothing left to do.
#eval do
  let (_, s) ← mkHandshakenPair

  discard <| s.feedEncrypted corruptRecord
  discard <| errorOf (s.read 128)
  assertDone "closeNotify on an aborted session" s.closeNotify

-- A session that never negotiated cannot carry plaintext `write` accepted, and flushing it would run
-- the handshake rather than complete a teardown. The data is lost either way, so the shutdown says
-- so instead of reporting the clean close it reports when nothing was pending.
#eval do
  let c ← mkClient
  discard <| c.write "never-sent".toUTF8
  assertRaises "before buffered data could be sent" "closeNotify holding queued plaintext"
    c.closeNotify

-- The same holds when the session was established and then torn down by a fatal error: a queue that
-- survives the abort must not be reported as a clean close. A write issued before the handshake is
-- the only way to still be holding plaintext once the session is up.
#eval do
  let (c, s) ← mkPair

  discard <| c.write "queued-payload".toUTF8
  runHandshake c s

  discard <| c.feedEncrypted corruptRecord
  discard <| errorOf (c.read 128)

  assertRaises "before buffered data could be sent"
    "closeNotify on an aborted session with queued plaintext" c.closeNotify

-- `closeNotify` decides "this session never negotiated, so there is nothing to close" from the
-- session's own handshake state rather than from whatever the failing `SSL_shutdown` happened to
-- leave in the error queue. A half-open handshake is the case that distinguishes the two: the
-- ClientHello has been produced, so the session is no longer untouched, but it is still in init.
#eval do
  let c ← mkClient
  discard <| c.handshake
  discard <| c.drainEncrypted
  assertDone "closeNotify mid-handshake" c.closeNotify

-- `read` reports the socket I/O the *queue* is waiting on, never one it invented: a blocked flush
-- supersedes the read's own want. Plaintext written before the handshake is the only way to hold a
-- blocked queue behind memory BIOs, and there OpenSSL wants encrypted input for both.
#eval do
  let c ← mkClient
  discard <| c.write "queued".toUTF8
  for (label, r) in [("peek", ← c.read 0), ("read", ← c.read 1024)] do
    match r with
    | .wantRead => pure ()
    | .data b => throw <| IO.userError s!"{label} returned data ({b.size} bytes) before the handshake"
    | .closed => throw <| IO.userError s!"{label} reported closed before the handshake"

-- The pending-write queue is bounded, so a caller that keeps writing while the session is blocked
-- is refused rather than allowed to buffer without limit. The first write is always admitted: a
-- blocked `SSL_write` consumed nothing but requires the same bytes and length back on retry, so
-- that payload has to be kept whatever its size.
#eval do
  let c ← mkClient
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

-- The bound is judged against a queue that has already been given its chance to drain. A backlog
-- queued before the handshake is gone the moment the session can encrypt, so a write that fits once
-- it drains has to be taken rather than refused against a backlog that is no longer there.
--
-- Refusing it does not merely lose one write: the raise returns before the flush that would have
-- cleared the queue, so nothing drains and the same payload is refused on every retry — the
-- `resourceExhausted` docstring promises it "can be passed again later", and it never can.
#eval do
  let (c, s) ← mkPair
  let queued : ByteArray := ⟨Array.replicate (512 * 1024) (0x41 : UInt8)⟩

  if ← c.write queued then
    throw <| IO.userError "a pre-handshake write should queue, not complete"

  runHandshake c s

  -- 600 KiB against a 1 MiB bound. Only a backlog measured before the flush leaves too little room.
  let more : ByteArray := ⟨Array.replicate (600 * 1024) (0x42 : UInt8)⟩
  assertOk "a write whose backlog would flush first" (c.write more)
  assertOk "the same write again" (c.write more)

  -- Nothing was dropped on the way: the peer sees every byte of all three writes.
  pipeEncrypted c s
  assertEqN (← drainPlaintext s).size.toUInt64 (512 * 1024 + 2 * 600 * 1024)
    "plaintext delivered across a flushed backlog"

-- `SSL_write` into a memory BIO never blocks, so the encrypted output — not the pending-write queue
-- — is the buffer that grows on an established session. A caller that keeps writing without draining
-- would otherwise hold an unbounded amount of ciphertext while every `write` reported success.
#eval do
  let (c, _) ← mkHandshakenPair
  let chunk : ByteArray := ⟨Array.replicate (512 * 1024) (0x41 : UInt8)⟩

  let mut refused := none
  for _ in [0:24] do
    if refused.isNone then
      refused := ← errorOf (c.write chunk)

  match refused with
  | none => throw <| IO.userError "the session buffered 12 MiB of undrained ciphertext without a bound"
  | some msg =>
    unless (msg.splitOn "undrained encrypted output").length > 1 do
      throw <| IO.userError s!"unexpected output-backlog error: {msg}"

  -- An empty write stays accepted at the bound, since flushing is part of the way back under it.
  assertOk "a pure flush against a full output backlog" (c.write ByteArray.empty)

  -- Draining is the way back: the same write is taken once the ciphertext has been collected.
  assertGt (← c.pendingEncrypted) 0 "pendingEncrypted before draining"
  discard <| c.drainEncrypted
  assertEqN (← c.pendingEncrypted) 0 "pendingEncrypted after draining"
  assertOk "a write after draining the encrypted backlog" (c.write chunk)

-- The bound is judged against what a write would *leave* behind, not against what is already there,
-- or one payload could carry the backlog past it by its own size. The exemption is a fully drained
-- session, which has nothing to pile onto -- otherwise a message larger than the bound could never
-- be sent at all.
#eval do
  let (c, _) ← mkHandshakenPair

  -- Nothing undrained, so an oversized payload is still accepted.
  assertOk "an oversized write against a drained session"
    (c.write ⟨Array.replicate (6 * 1024 * 1024) (0x41 : UInt8)⟩)

  -- With that sitting undrained, even a small write is refused rather than piled on top.
  assertRaises "undrained encrypted output" "a small write onto an over-full backlog"
    (c.write "one more".toUTF8)

  discard <| c.drainEncrypted
  assertOk "the same small write once the backlog is gone" (c.write "one more".toUTF8)

-- The case that separates the two readings of the bound: a backlog still *under* it, and a payload
-- that carries it over. Judged against what is already there, this write is admitted and leaves the
-- session holding more than the bound allows; judged against what it would leave behind, it is
-- refused. The test above passes either way, so this is the one that pins the rule.
#eval do
  let (c, _) ← mkHandshakenPair
  discard <| c.drainEncrypted

  -- Comfortably under the 4 MiB bound, so nothing refuses this on either reading.
  assertOk "a write that stays under the bound"
    (c.write ⟨Array.replicate (3 * 1024 * 1024) (0x41 : UInt8)⟩)

  let unsent ← c.pendingEncrypted
  unless unsent > 2 * 1024 * 1024 && unsent < 4 * 1024 * 1024 do
    throw <| IO.userError
      s!"the backlog has to sit under the bound for this case to bite, but is {unsent}"

  assertRaises "undrained encrypted output" "a write that would carry the backlog past the bound"
    (c.write ⟨Array.replicate (2 * 1024 * 1024) (0x41 : UInt8)⟩)

-- An empty feed asks the session to take nothing, so no state it could be in makes that an error.
-- A transport pump that reports a zero-length socket read has not done anything wrong.
#eval do
  let (c, s) ← mkHandshakenPair

  s.feedEof
  assertOk "an empty feed after feedEof" (s.feedEncrypted ByteArray.empty)
  assertRaises "already ended" "a real feed after feedEof" (s.feedEncrypted "late".toUTF8)

  discard <| s.closeNotify
  pipeEncrypted s c
  discard <| c.read 1024
  assertOk "an empty feed after the peer's close_notify" (c.feedEncrypted ByteArray.empty)

-- The input BIO is the buffer a hostile *peer* grows: a pump that keeps feeding a socket while the
-- application is slow to read would otherwise hold unbounded ciphertext, with nothing reporting how
-- much of it there is. `feedEncrypted` bounds it and `pendingEncryptedInput` measures it.
#eval do
  let (c, s) ← mkHandshakenPair

  -- Fresh records every round: a TLS record carries a sequence number, so re-feeding one the peer
  -- already sent fails to authenticate rather than testing the bound.
  let mut refused := none
  let mut turnedAway := ByteArray.empty
  for _ in [0:24] do
    if refused.isNone then
      discard <| c.write ⟨Array.replicate (512 * 1024) (0x41 : UInt8)⟩
      let ciphertext ← c.drainEncrypted
      match ← errorOf (s.feedEncrypted ciphertext) with
      | none => pure ()
      | some msg =>
        refused := some msg
        turnedAway := ciphertext

  match refused with
  | none => throw <| IO.userError "the session buffered 12 MiB of unread ciphertext without a bound"
  | some msg =>
    unless (msg.splitOn "unread encrypted input").length > 1 do
      throw <| IO.userError s!"unexpected input-backlog error: {msg}"

  -- The accessor reports what is held, and reading is the way back under the bound. The refused
  -- bytes were never taken, so the stream resumes exactly where it stopped.
  assertGt (← s.pendingEncryptedInput) 0 "pendingEncryptedInput before reading"
  discard <| drainPlaintext s
  assertEqN (← s.pendingEncryptedInput) 0 "pendingEncryptedInput after reading"
  assertOk "feedEncrypted after draining the input backlog" (s.feedEncrypted turnedAway)
  assertEqN (← drainPlaintext s).size.toUInt64 (512 * 1024) "the refused chunk arrives intact on retry"

-- Until the transport reports EOF, an empty input BIO is indistinguishable from "the next bytes
-- have not arrived yet", so a peer that vanishes without `close_notify` would leave `read` asking
-- for input forever. `feedEof` turns that into the truncation error it actually is.
#eval do
  let (c, _) ← mkHandshakenPair

  match ← c.read 128 with
  | .wantRead => pure ()
  | _ => throw <| IO.userError "expected the client to be waiting on input before feedEof"

  c.feedEof
  assertRaises "end of file" "read after feedEof" (c.read 128)

  -- The stream is over, so further encrypted input is a caller error rather than a silent resume.
  assertRaises "already ended" "feedEncrypted after feedEof" (c.feedEncrypted "late".toUTF8)

-- `feedEof` marks the end of the stream, not the end of what has been read: bytes already fed stay
-- readable, and a `close_notify` among them still ends the session cleanly rather than as a
-- truncation.
#eval do
  let (c, s) ← mkHandshakenPair

  discard <| s.write "last".toUTF8
  discard <| s.closeNotify
  pipeEncrypted s c
  c.feedEof

  match ← c.read 1024 with
  | .data b => assertEqStr (String.fromUTF8! b) "last"
  | .closed => throw <| IO.userError "feedEof discarded plaintext that had already been fed"
  | .wantRead => throw <| IO.userError "expected the buffered record after feedEof"

  match ← c.read 1024 with
  | .closed => pure ()
  | .data b => throw <| IO.userError s!"unexpected data ({b.size} bytes) after the peer's close_notify"
  | .wantRead => throw <| IO.userError "expected .closed for a close_notify received before feedEof"

-- A single `write` larger than the queue bound is admitted, since `SSL_write` has already taken the
-- payload by then. The bound still has to hold for everything written afterwards, even though the
-- queue is now sitting above it.
#eval do
  let c ← mkClient

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
  assertOk "a pure flush against a full queue" (c.write ByteArray.empty)

-- The server name feeds the `ClientHello`, so it is too late to set once the handshake has started
-- even though the session is not yet established: SNI would go unsent while the caller was told it
-- had been applied.
#eval do
  let c ← mkClient
  discard <| c.handshake

  assertRaises "before the handshake starts" "setServerName after the ClientHello"
    (c.setServerName "example.com")

-- OpenSSL diagnoses a truncated stream once and then reports the session as a generic failure, so
-- the truncation has to be remembered: every `read` after the transport ends must agree.
#eval do
  let (c, _) ← mkHandshakenPair

  c.feedEof
  assertRaises "end of file" "read after feedEof" (c.read 1024)
  assertRaises "end of file" "repeated read after feedEof" (c.read 1024)
  assertRaises "end of file" "peek after feedEof" c.peek

-- Teardown runs on exactly the connections whose peer vanishes without answering our alert, so a
-- transport that ends there is the expected outcome rather than an error to catch.
#eval do
  let (c, _) ← mkHandshakenPair

  assertWantRead "the first closeNotify awaits the peer's alert" c.closeNotify

  discard <| c.drainEncrypted
  c.feedEof

  for i in [0:3] do
    assertDone s!"closeNotify #{i} after a half-close" c.closeNotify

-- A peer's `close_notify` sent behind a final record is buffered the moment that flight arrives, but
-- OpenSSL cannot report it without consuming the record first — and a shutdown must not consume
-- plaintext. Reporting `.read` there would strand a caller looping on `closeNotify` alone: the alert
-- it is told to wait for has already arrived, so no further input can ever come. Looping on
-- `closeNotify` must terminate whether or not the caller interleaves `read`.
#eval do
  let (c, s) ← mkHandshakenPair

  discard <| s.write "final-record".toUTF8
  discard <| s.closeNotify
  discard <| c.feedEncrypted (← s.drainEncrypted)

  for i in [0:3] do
    assertDone s!"closeNotify #{i} asked for input that had already arrived" c.closeNotify

  -- The shutdown reported done, but the plaintext behind which the alert sat is still there.
  match ← c.read 1024 with
  | .data b => assertEqStr (String.fromUTF8! b) "final-record"
  | .closed => throw <| IO.userError "closeNotify discarded the plaintext it stopped short of"
  | .wantRead => throw <| IO.userError "expected the buffered plaintext after the shutdown"

  -- Draining the rest reaches the peer's alert, completing the bidirectional shutdown.
  match ← c.read 1024 with
  | .closed => pure ()
  | _ => throw <| IO.userError "expected the peer's close_notify behind the record"

  assertDone "shutdown did not complete after the alert was read" c.closeNotify

-- A fatal error is diagnosed by OpenSSL exactly once; afterwards `SSL_in_init`, `SSL_get_shutdown`
-- and `SSL_want` read the same as on a session that is merely waiting for input, so an undefended
-- retry is told to wait for socket I/O that can never arrive. Every operation must keep reporting
-- the failure instead. The garbage below is chosen for the record header OpenSSL rejects without
-- leaving anything queued, which is the case that degrades; other malformed input re-raises by
-- itself and would not exercise this.
#eval do
  let (c, s) ← mkPair

  -- The client is waiting for a ServerHello; hand it a record with an unusable version instead.
  discard <| c.handshake
  discard <| s.feedEncrypted (← c.drainEncrypted)
  discard <| c.feedEncrypted (ByteArray.mk (List.replicate 64 (0x16 : UInt8)).toArray)

  assertRaises "unrecognized version" "a bogus record during the handshake" c.handshake

  -- The session is dead. Nothing may report progress or ask for input again.
  let aborted := "aborted by an earlier fatal error"
  for i in [0:3] do
    assertRaises aborted s!"handshake #{i} on a dead session" c.handshake
    assertRaises aborted s!"write #{i} on a dead session" (c.write "x".toUTF8)
    assertRaises aborted s!"read #{i} on a dead session" (c.read 1024)
    assertRaises aborted s!"peek #{i} on a dead session" c.peek
    -- `SSL_get0_peername` keeps answering after a verification that failed, since the name is
    -- recorded before the checks that reject the certificate. Reporting it would name a peer this
    -- session never authenticated.
    assertRaises aborted s!"peerName #{i} on a dead session" c.peerName

-- A truncated stream keeps its own classification: `failed` alone would turn the end of the stream
-- into a protocol error, which a caller cannot distinguish from a peer that spoke garbage.
#eval do
  let (c, _) ← mkHandshakenPair
  c.feedEof

  assertRaises "end of file" "read after feedEof" (c.read 1024)
  assertRaises "end of file" "repeated read after feedEof" (c.read 1024)
  assertRaises "end of file" "handshake after feedEof" c.handshake

-- Teardown must not depend on whether the caller happened to read first. The same broken session
-- reaches `closeNotify` by two routes -- with the failure already diagnosed, and with `closeNotify`
-- itself the first call to touch the bad input -- and both must report the same clean close.
#eval do
  let mk : IO Session.Server := do
    let (_, s) ← mkHandshakenPair
    discard <| s.feedEncrypted corruptRecord
    return s

  -- Route A: a read diagnoses the corrupt record, then teardown runs.
  let a ← mk
  discard <| errorOf (a.read 1024)
  assertDone "closeNotify after the failure was diagnosed" a.closeNotify

  -- Route B: teardown is the first call to see the corrupt record.
  let b ← mk
  assertDone "closeNotify on an undiagnosed failure" b.closeNotify

  -- Both sessions stay torn down, and repeated teardown stays a no-op.
  for (label, sess) in [("A", a), ("B", b)] do
    for i in [0:2] do
      assertDone s!"closeNotify {label} #{i}" sess.closeNotify

-- The one loss a caller has to hear about on teardown is plaintext `write` accepted but never
-- delivered, and a session killed before it could be flushed is exactly that case.
#eval do
  let (c, s) ← mkPair

  -- Queued before the handshake, so it is still waiting when the session dies.
  if ← c.write "never-sent".toUTF8 then
    throw <| IO.userError "a pre-handshake write should be queued, not accepted outright"

  discard <| s.feedEncrypted (← c.drainEncrypted)
  discard <| c.feedEncrypted (ByteArray.mk (List.replicate 64 (0x16 : UInt8)).toArray)
  discard <| errorOf c.handshake

  assertRaises "before buffered data could be sent" "closeNotify after the session was killed"
    c.closeNotify

-- Reporting undelivered plaintext is what a teardown path has to hear, but only once: a `finally`
-- or a retry loop calls `closeNotify` again, and a session that has already reported the loss has
-- nothing left to say about it.
#eval do
  let c ← mkClient
  discard <| c.write "never-sent".toUTF8

  assertRaises "before buffered data could be sent" "the first closeNotify" c.closeNotify

  for i in [0:3] do
    assertDone s!"closeNotify #{i} repeating a reported loss" c.closeNotify

-- `setServerName` drives nothing, so `SSL_in_before` still reads true on a session teardown already
-- finished — it has to consult the session's own verdict instead. Accepting a name there would tell
-- the caller a peer identity had been configured for a handshake that can never run.
#eval do
  let c ← mkClient
  discard <| c.closeNotify

  assertRaises "closed before it was negotiated" "setServerName on a closed session"
    (c.setServerName "example.com")

-- An address and a hostname are separate reference identities to OpenSSL, and before 3.5 setting
-- one left the other in place. A second `setServerName` must replace the first outright, or the
-- handshake is verified against a name the caller has withdrawn and fails on a valid certificate.
-- OpenSSL 3.5 and later clear both identities themselves, so this only bites on older builds.
#eval do
  let (c, s) ← mkVerifyingPair

  -- The withdrawn IP must not still be checked against a certificate that names only hosts.
  c.setServerName "192.0.2.1"
  c.setServerName testHost

  runHandshake c s
  assertEqN (← c.verifyResult) 0 "verifyResult after replacing an IP server name with a hostname"

-- A received fatal alert is queued as `SSL_AD_REASON_OFFSET` plus its descriptor, so the whole band
-- at and above that offset has to decode as an alert. `close_notify` is descriptor 0, which lands on
-- the offset exactly: sent at fatal level it is not absorbed as a clean shutdown, so it reaches the
-- error queue as reason 1000. An exclusive bound drops it through to the generic handshake message.
#eval do
  let c ← mkClient

  -- Drive the ClientHello out so the session is waiting on the server's flight.
  discard <| c.handshake
  discard <| c.drainEncrypted

  -- An unencrypted alert record: content type 21, TLS 1.2 record version, level 2 (fatal),
  -- description 0 (close_notify).
  discard <| c.feedEncrypted (ByteArray.mk #[0x15, 0x03, 0x03, 0x00, 0x02, 0x02, 0x00])

  assertRaises "fatal alert" "a fatal-level close_notify during the handshake" c.handshake

-- `SSL_write` is refused once our own `close_notify` has gone out, but that closes only the write
-- direction: records the peer sent before it saw the alert are still decrypted and waiting. Treating
-- the refusal as fatal would finish the session and strand them.
#eval do
  let (c, s) ← mkHandshakenPair

  discard <| s.write "peer-record".toUTF8
  discard <| c.closeNotify
  pipeEncrypted s c

  assertRaises "already shut down" "a write after our own close_notify" (c.write "oops".toUTF8)

  match ← c.read 1024 with
  | .data bytes => assertEqStr (String.fromUTF8! bytes) "peer-record"
  | _ => throw <| IO.userError "the peer's records were lost by a refused write"

-- A `write` refused after our own `close_notify` was never accepted, so there is no plaintext to
-- lose and the teardown that follows is a clean one. `write` queues the payload before offering it
-- to `SSL_write`, and the refusal leaves it there, so a session that reports the loss is reporting
-- bytes it declined to take -- out of the `closeNotify` a teardown path runs unconditionally.
#eval do
  let (c, _) ← mkHandshakenPair

  discard <| c.closeNotify

  assertRaises "already shut down" "a write after our own close_notify" (c.write "refused".toUTF8)
  assertWantRead "closeNotify after a refused write" c.closeNotify

-- `feedEof` fixes the diagnosis of a session that never negotiated, so `closeNotify` and `read` have
-- to agree on it whichever runs first. `SSL_shutdown` refuses to run in init and never reads, so the
-- shutdown path cannot get the verdict from OpenSSL the way the read path does.
#eval do
  let readFirst ← do
    let c ← mkClient
    discard <| c.handshake
    discard <| c.drainEncrypted
    c.feedEof
    errorOf (c.read 1024)

  let closeFirst ← do
    let c ← mkClient
    discard <| c.handshake
    discard <| c.drainEncrypted
    c.feedEof
    discard <| c.closeNotify
    errorOf (c.read 1024)

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
  let helloSize (host : String) : IO Nat := do
    let c ← mkClient
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
  let helloSize (host : String) : IO Nat := do
    let c ← mkClient
    c.setServerName host
    discard <| c.handshake
    return (← c.drainEncrypted).size

  let absolute ← helloSize (testHost ++ ".")
  let relative ← helloSize testHost

  unless absolute == relative do
    throw <| IO.userError
      s!"a trailing dot reached the SNI extension: ClientHello {absolute} vs {relative}"

-- The stripped dot must leave the hostname bound for verification too, not just shorten the SNI.
#eval do
  let (c, s) ← mkVerifyingPair

  -- The certificate names the host without the dot, which only matches once the dot is gone.
  c.setServerName (testHost ++ ".")

  runHandshake c s
  assertEqN (← c.verifyResult) 0 "verifyResult for an absolute FQDN server name"

-- A bare `"."` is the root, which strips to nothing. It has to be refused as an empty name rather
-- than reaching `SSL_set1_host`, which answers success for one and verifies against nothing.
#eval do
  let c ← mkClient
  assertRaises "the server name is empty" "a bare '.' server name" (c.setServerName ".")

-- A URI authority reserves the bracketed form for an address, so a bracketed name that is not one is
-- malformed. Accepting it would put the brackets on the wire as SNI and bind the peer to a name no
-- certificate can carry, surfacing a round trip later as a certificate mismatch. A scope id is the
-- realistic way to get here: `a2i_IPADDRESS` does not accept one, so `[fe80::1%25eth0]` — a
-- well-formed RFC 6874 authority — falls out of the address branch.
#eval do
  for host in ["[a]", "[]", "[::1", "[fe80::1%25eth0]"] do
    let c ← mkClient
    assertRaises "not a valid IP address" s!"the bracketed server name {host}" (c.setServerName host)

  -- The bracketed forms that do parse as an address stay accepted, trailing dot and all.
  for host in ["[::1]", "[::1].", "[1.2.3.4]"] do
    let c ← mkClient
    assertOk s!"the bracketed address {host}" (c.setServerName host)

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
  let c ← mkClient

  discard <| c.handshake
  discard <| c.drainEncrypted
  discard <| c.feedEncrypted tls12BadCertificateFlight

  -- One diagnosis, checked both ways: the session is dead after it, so a second call would report
  -- the recorded failure instead.
  match ← errorOf c.handshake with
  | none => throw <| IO.userError "an unparseable peer certificate must fail the handshake"
  | some msg =>
    if (msg.splitOn "fatal alert").length > 1 then
      throw <| IO.userError s!"a local certificate-parse failure was blamed on the peer: {msg}"
    unless (msg.splitOn "the TLS handshake failed").length > 1 do
      throw <| IO.userError s!"unexpected unparseable-certificate error: {msg}"
