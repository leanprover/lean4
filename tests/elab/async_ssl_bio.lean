import Std.Async.TCP.SSL
import Std.Net.Addr

/-!
Tests for `Std.Async.TCP.SSL`: in-process memory-BIO `Session` behaviour (handshake, data, `close_notify`).
-/

open Std Async TCP.SSL
open Std.Net
open Std.Internal.SSL


def assertEqStr (actual expected : String) : IO Unit := do
  unless actual == expected do
    throw <| IO.userError s!"expected '{expected}', got '{actual}'"

def assertGt (actual : UInt64) (bound : UInt64) (label : String) : IO Unit := do
  unless actual > bound do
    throw <| IO.userError s!"{label}: expected > {bound}, got {actual}"

def assertEqN (actual expected : UInt64) (label : String) : IO Unit := do
  unless actual == expected do
    throw <| IO.userError s!"{label}: expected {expected}, got {actual}"

def setupTestCerts : IO (String × String) := do
  let dir ← IO.FS.createTempDir
  let keyFile  := toString (dir / "key.pem")
  let certFile := toString (dir / "cert.pem")

  let keyOut ← IO.Process.output {
    cmd  := "openssl"
    args := #["genrsa", "-out", keyFile, "2048"]
  }
  unless keyOut.exitCode == 0 do
    throw <| IO.userError s!"openssl genrsa failed: {keyOut.stderr}"

  let certOut ← IO.Process.output {
    cmd  := "openssl"
    args := #["req", "-new", "-x509", "-key", keyFile, "-out", certFile, "-days", "1", "-subj", "/CN=localhost"]
  }
  unless certOut.exitCode == 0 do
    throw <| IO.userError s!"openssl req failed: {certOut.stderr}"

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

def testContextCreation (certFile keyFile : String) : IO Unit := do
  let serverCtx ← Context.Server.mk certFile keyFile

  let clientCtx ← Context.Client.mk "" false

  -- Configuring with a CA file path (non-empty) exercises the other branch.
  let clientCtx2 ← Context.Client.mk certFile false

def testConfigureClientFromPEM (certFile keyFile : String) : IO Unit := do
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

  let clientCtx ← Context.Client.mk "" false  -- skip peer verification

  let serverSess ← Session.Server.mk serverCtx
  let clientSess ← Session.Client.mk clientCtx

  -- setServerName exercises SSL_set_tlsext_host_name.
  clientSess.setServerName "localhost"

  runHandshake clientSess serverSess

  -- verifyResult: just verify the call succeeds (self-signed cert returns
  -- X509_V_ERR_DEPTH_ZERO_SELF_SIGNED_CERT even with VERIFY_NONE).
  discard <| clientSess.verifyResult

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

def testEmptyWrite (certFile keyFile : String) : IO Unit := do
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false

  let serverSess ← Session.Server.mk serverCtx
  let clientSess ← Session.Client.mk clientCtx
  runHandshake clientSess serverSess

  let result ← clientSess.write ByteArray.empty
  unless result.isNone do
    throw <| IO.userError "empty write should return none"

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

def testVerifyResultString (certFile keyFile : String) : IO Unit := do
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false

  let serverSess ← Session.Server.mk serverCtx
  let clientSess ← Session.Client.mk clientCtx
  runHandshake clientSess serverSess

  let s ← clientSess.verifyResultString
  if s.isEmpty then
    throw <| IO.userError "verifyResultString returned empty string"

def testCloseNotify (certFile keyFile : String) : IO Unit := do
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false

  let serverSess ← Session.Server.mk serverCtx
  let clientSess ← Session.Client.mk clientCtx
  runHandshake clientSess serverSess

  -- Initiate shutdown from the client side.
  -- SSL_shutdown (rc=0) means our close_notify was sent; waiting for peer's.
  discard <| Session.closeNotify clientSess
  -- Deliver client's close_notify bytes to the server.
  pipeEncrypted clientSess serverSess
  -- Server calls SSL_shutdown; since it already received the client's
  -- close_notify and now sends its own, rc should be 1 (bidirectional done).
  discard <| Session.closeNotify serverSess
  -- Deliver server's close_notify back to the client.
  pipeEncrypted serverSess clientSess
  -- A second client closeNotify should now return none (done).
  discard <| Session.closeNotify clientSess

def testExactSizeRead (certFile keyFile : String) : IO Unit := do
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false

  let serverSess ← Session.Server.mk serverCtx
  let clientSess ← Session.Client.mk clientCtx
  runHandshake clientSess serverSess

  let payload := "exactread".toUTF8   -- 9 bytes
  discard <| clientSess.write payload
  pipeEncrypted clientSess serverSess

  let result ← serverSess.read? 9
  match result with
  | .data bytes =>
    unless bytes.size == 9 do
      throw <| IO.userError s!"exact-size read: expected 9 bytes, got {bytes.size}"
    unless bytes == payload do
      throw <| IO.userError "exact-size read: content mismatch"
  | _ => throw <| IO.userError "exact-size read: expected .data"

def testVerifyResultCode (certFile keyFile : String) : IO Unit := do
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false   -- VERIFY_NONE

  let serverSess ← Session.Server.mk serverCtx
  let clientSess ← Session.Client.mk clientCtx
  runHandshake clientSess serverSess

  -- verifyResult returns a numeric code; verifyResultString returns its description.
  -- We just check that the call succeeds and returns a non-empty string.
  let s ← Session.verifyResultString clientSess
  unless s.length > 0 do
    throw <| IO.userError "verifyResult: verifyResultString returned empty string after handshake"

def testCloseNotifySequenceBIO (certFile keyFile : String) : IO Unit := do
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false

  let serverSess ← Session.Server.mk serverCtx
  let clientSess ← Session.Client.mk clientCtx
  runHandshake clientSess serverSess

  -- Phase 1: client initiates shutdown.
  discard <| clientSess.closeNotify
  pipeEncrypted clientSess serverSess

  -- Phase 2: server receives client close_notify and sends its own.
  let w2 ← serverSess.closeNotify
  pipeEncrypted serverSess clientSess

  -- Phase 3: client receives server close_notify → bidirectional done.
  let w3 ← clientSess.closeNotify

  match w2 with
  | some _ => throw <| IO.userError "closeNotify sequence: server returned Some after receiving client alert"
  | none   => pure ()
  match w3 with
  | some _ => throw <| IO.userError "closeNotify sequence: client returned Some after bidirectional shutdown"
  | none   => pure ()

def testReadWithPendingData (certFile keyFile : String) : IO Unit := do
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false

  let serverSess ← Session.Server.mk serverCtx
  let clientSess ← Session.Client.mk clientCtx
  runHandshake clientSess serverSess

  let msg := "no-want-write".toUTF8
  discard <| clientSess.write msg
  pipeEncrypted clientSess serverSess

  match ← serverSess.read? 1024 with
  | .data bytes =>
    unless String.fromUTF8! bytes == "no-want-write" do
      throw <| IO.userError "readWithPendingData: data mismatch"
  | .wantIO _ => throw <| IO.userError "readWithPendingData: WANT_IO with data in BIO"
  | .closed   => throw <| IO.userError "readWithPendingData: unexpected closed"

def testPlaintextBeforeCloseNotify (certFile keyFile : String) : IO Unit := do
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false

  let serverSess ← Session.Server.mk serverCtx
  let clientSess ← Session.Client.mk clientCtx
  runHandshake clientSess serverSess

  let payload := ByteArray.mk ((Array.range 200).map (fun i => (i % 256).toUInt8))
  discard <| serverSess.write payload
  let encData  ← serverSess.drainEncrypted

  discard <| serverSess.closeNotify
  let encClose ← serverSess.drainEncrypted

  -- Feed both chunks at once so close_notify is already queued when reading starts.
  discard <| clientSess.feedEncrypted encData
  discard <| clientSess.feedEncrypted encClose

  let mut total := 0
  let mut stop  := false
  while !stop do
    match ← clientSess.read? 50 with
    | .data b   => total := total + b.size
    | .closed   => stop := true
    | .wantIO _ => stop := true
  unless total == 200 do
    throw <| IO.userError s!"plaintextBeforeCloseNotify: received {total}/200 bytes before .closed"

#eval do
  let (certFile, keyFile) ← setupTestCerts
  testContextCreation certFile keyFile

#eval do
  let (certFile, keyFile) ← setupTestCerts
  testConfigureClientFromPEM certFile keyFile

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
  testCloseNotify certFile keyFile

#eval do
  let (certFile, keyFile) ← setupTestCerts
  testExactSizeRead certFile keyFile

#eval do
  let (certFile, keyFile) ← setupTestCerts
  testVerifyResultCode certFile keyFile

#eval do
  let (certFile, keyFile) ← setupTestCerts
  testCloseNotifySequenceBIO certFile keyFile

#eval do
  let (certFile, keyFile) ← setupTestCerts
  testReadWithPendingData certFile keyFile

#eval do
  let (certFile, keyFile) ← setupTestCerts
  testPlaintextBeforeCloseNotify certFile keyFile
