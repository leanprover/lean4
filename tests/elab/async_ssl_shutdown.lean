import Std.Async.TCP.SSL
import Std.Net.Addr

/-!
Tests for `Std.Async.TCP.SSL`: TLS/TCP shutdown, `close_notify`, and truncation handling.
-/

open Std Async TCP.SSL
open Std.Net
open Std.Internal.SSL


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

def testRecvAfterShutdown (addr : SocketAddress) (certFile keyFile : String) : IO Unit := do
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false

  let server ← Server.mk serverCtx
  server.bind addr
  server.listen 128

  let srvTask ← (do
    let conn ← server.accept
    let msg ← conn.recv? 1024
    conn.send (msg.getD ByteArray.empty)
    Async.ofPromise conn.native.shutdown  -- server closes write side first
  : Async Unit).toIO

  let cliTask ← (do
    let client ← Client.mk clientCtx (some "localhost")
    client.connect addr
    client.send "ping".toUTF8
    -- Receive the echo
    let resp ← client.recv? 1024
    let got := String.fromUTF8! (resp.getD ByteArray.empty)
    unless got == "ping" do
      throw <| IO.userError s!"echo mismatch: '{got}'"
    -- After server TCP-only shutdown (no close_notify), recv? must throw a
    -- truncation error, not silently return none.
    try
      let _ ← client.recv? 1024
      throw <| IO.userError "expected truncation error after server TCP-only shutdown"
    catch e =>
      let msg := toString e
      unless msg.contains "truncation" || msg.contains "close_notify" do
        throw e
    Async.ofPromise client.native.shutdown
  : Async Unit).toIO

  srvTask.block
  cliTask.block

def testTLSShutdown (addr : SocketAddress) (certFile keyFile : String) : IO Unit := do
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false

  let server ← Server.mk serverCtx
  server.bind addr
  server.listen 128

  let srvTask ← (do
    let conn ← server.accept
    let msg ← conn.recv? 1024
    conn.send (msg.getD ByteArray.empty)
    conn.tlsShutdown  -- proper TLS close
  : Async Unit).toIO

  let cliTask ← (do
    let client ← Client.mk clientCtx (some "localhost")
    client.connect addr
    client.send "shutdown-test".toUTF8
    let resp ← client.recv? 1024
    let got := String.fromUTF8! (resp.getD ByteArray.empty)
    unless got == "shutdown-test" do
      throw <| IO.userError s!"shutdown round-trip mismatch: '{got}'"
    client.tlsShutdown  -- proper TLS close on client too
  : Async Unit).toIO

  srvTask.block
  cliTask.block

def testRecvAfterTCPClose (addr : SocketAddress) (certFile keyFile : String) : IO Unit := do
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false

  let server ← Server.mk serverCtx
  server.bind addr
  server.listen 128

  let srvTask ← (do
    let conn ← server.accept
    Async.ofPromise conn.native.shutdown  -- TCP-only close, no TLS close_notify
  : Async Unit).toIO

  let cliTask ← (do
    let client ← Client.mk clientCtx (some "localhost")
    client.connect addr
    -- recv? must throw a truncation error (not silently return none) when the
    -- peer closes TCP without sending a close_notify alert.
    try
      let _ ← client.recv? 1024
      throw <| IO.userError "recv? after TCP-only close: expected truncation error, got none"
    catch e =>
      let msg := toString e
      unless msg.contains "truncation" || msg.contains "close_notify" do
        throw e
    Async.ofPromise client.native.shutdown
  : Async Unit).toIO

  srvTask.block
  cliTask.block

def testRecvAfterTLSShutdown (addr : SocketAddress) (certFile keyFile : String) : IO Unit := do
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false

  let server ← Server.mk serverCtx
  server.bind addr
  server.listen 128

  let srvTask ← (do
    let conn ← server.accept
    conn.send "before-close".toUTF8
    conn.tlsShutdown
  : Async Unit).toIO

  let cliTask ← (do
    let client ← Client.mk clientCtx (some "localhost")
    client.connect addr
    -- Consume the message sent before shutdown.
    let msg ← client.recv? 1024
    let got := String.fromUTF8! (msg.getD ByteArray.empty)
    unless got == "before-close" do
      throw <| IO.userError s!"recv after tlsShutdown: expected 'before-close', got '{got}'"
    -- After the server's tlsShutdown, recv? must return none.
    let closed ← client.recv? 1024
    unless closed.isNone do
      throw <| IO.userError "recv after tlsShutdown: expected none after server tlsShutdown"
    client.tlsShutdown
  : Async Unit).toIO

  srvTask.block
  cliTask.block

def testTCPTruncationDetection (addr : SocketAddress) (certFile keyFile : String) : IO Unit := do
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false

  let server ← Server.mk serverCtx
  server.bind addr
  server.listen 128

  let srvTask ← (do
    let conn ← server.accept
    conn.send "hello".toUTF8
    Async.ofPromise conn.native.shutdown   -- TCP-only close, no TLS close_notify
  : Async Unit).toIO

  let cliTask ← (do
    let client ← Client.mk clientCtx (some "localhost")
    client.connect addr
    let _ ← client.recv? 1024
    -- Second recv? must throw (truncation), not silently return none.
    let threw ← try
      let _ ← client.recv? 1024
      pure false
    catch _ =>
      pure true
    unless threw do
      throw <| IO.userError
        "testTCPTruncationDetection: recv? returned none after TCP-only shutdown — \
         truncation was not detected"
  : Async Unit).toIO

  srvTask.block
  cliTask.block

#eval do
  let (certFile, keyFile) ← setupTestCerts
  testRecvAfterShutdown (SocketAddressV4.mk (.ofParts 127 0 0 1) 18447) certFile keyFile

#eval do
  let (certFile, keyFile) ← setupTestCerts
  testTLSShutdown (SocketAddressV4.mk (.ofParts 127 0 0 1) 18453) certFile keyFile

#eval do
  let (certFile, keyFile) ← setupTestCerts
  testRecvAfterTCPClose (SocketAddressV4.mk (.ofParts 127 0 0 1) 18456) certFile keyFile

#eval do
  let (certFile, keyFile) ← setupTestCerts
  testRecvAfterTLSShutdown (SocketAddressV4.mk (.ofParts 127 0 0 1) 18459) certFile keyFile

#eval do
  let (certFile, keyFile) ← setupTestCerts
  testTCPTruncationDetection (SocketAddressV4.mk (.ofParts 127 0 0 1) 18465) certFile keyFile
