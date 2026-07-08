import Std.Async.TCP.SSL
import Std.Net.Addr

/-!
Tests for `Std.Async.TCP.SSL`: full TCP round-trips and data transfer over the TLS socket API.
-/

open Std Async TCP.SSL
open Std.Net
open Std.Internal.SSL


def assertEqStr (actual expected : String) : IO Unit := do
  unless actual == expected do
    throw <| IO.userError s!"expected '{expected}', got '{actual}'"

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

def serverTask (server : TCP.SSL.Server) : Async Unit := do
  let client ← server.accept
  let msg ← client.recv? 1024
  client.send (msg.getD ByteArray.empty)  -- echo
  Async.ofPromise client.native.shutdown

def clientTask (addr : SocketAddress) (clientCtx : Context.Client) : Async Unit := do
  let client ← Client.mk clientCtx (some "localhost")
  client.connect addr
  client.noDelay
  client.send "hello over tls".toUTF8
  let resp ← client.recv? 1024
  let got := String.fromUTF8! (resp.getD ByteArray.empty)
  unless got == "hello over tls" do
    throw <| IO.userError s!"round-trip mismatch: '{got}'"
  let _ ← client.getPeerName
  let _ ← client.getSockName
  let _ ← client.verifyResult
  Async.ofPromise client.native.shutdown

def testTCPSSL (addr : SocketAddress) (certFile keyFile : String) : IO Unit := do
  let serverCtx ← Context.Server.mk certFile keyFile

  let clientCtx ← Context.Client.mk "" false

  let server ← Server.mk serverCtx
  server.bind addr
  server.listen 128

  let _ ← server.getSockName

  let srvTask ← (serverTask server).toIO
  let cliTask ← (clientTask addr clientCtx).toIO

  srvTask.block
  cliTask.block

def testMultipleRoundTrips (addr : SocketAddress) (certFile keyFile : String) : IO Unit := do
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false

  let server ← Server.mk serverCtx
  server.bind addr
  server.listen 128

  let srvTask ← (do
    let conn ← server.accept
    for _ in List.range 5 do
      let msg ← conn.recv? 1024
      conn.send (msg.getD ByteArray.empty)
    Async.ofPromise conn.native.shutdown
  : Async Unit).toIO

  let cliTask ← (do
    let client ← Client.mk clientCtx (some "localhost")
    client.connect addr
    for i in List.range 5 do
      let payload := s!"msg{i}".toUTF8
      client.send payload
      let resp ← client.recv? 1024
      let got := String.fromUTF8! (resp.getD ByteArray.empty)
      unless got == s!"msg{i}" do
        throw <| IO.userError s!"round-trip {i} mismatch: '{got}'"
    Async.ofPromise client.native.shutdown
  : Async Unit).toIO

  srvTask.block
  cliTask.block

def testLargePayload (addr : SocketAddress) (certFile keyFile : String) : IO Unit := do
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false

  -- 64 KB + 1: spans multiple TLS records and multiple `send` chunks, with a final partial
  -- chunk. The position-dependent pattern catches dropped, duplicated, or reordered chunks
  -- that a constant fill would miss.
  let payloadSize := 64 * 1024 + 1
  let payload := ByteArray.mk ((Array.range payloadSize).map (·.toUInt8))

  let server ← Server.mk serverCtx
  server.bind addr
  server.listen 128

  let srvTask ← (do
    let conn ← server.accept
    -- Accumulate until we have all bytes, then echo back.
    let mut buf := ByteArray.empty
    while buf.size < payloadSize do
      let chunk ← conn.recv? (payloadSize - buf.size).toUInt64
      buf := buf ++ chunk.getD ByteArray.empty
    conn.send buf
    Async.ofPromise conn.native.shutdown
  : Async Unit).toIO

  let cliTask ← (do
    let client ← Client.mk clientCtx (some "localhost")
    client.connect addr
    client.send payload
    let mut buf := ByteArray.empty
    while buf.size < payloadSize do
      let chunk ← client.recv? (payloadSize - buf.size).toUInt64
      buf := buf ++ chunk.getD ByteArray.empty
    unless buf.size == payloadSize do
      throw <| IO.userError s!"large payload size mismatch: {buf.size}"
    unless buf == payload do
      throw <| IO.userError "large payload content mismatch"
    Async.ofPromise client.native.shutdown
  : Async Unit).toIO

  srvTask.block
  cliTask.block

def testSendAll (addr : SocketAddress) (certFile keyFile : String) : IO Unit := do
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false

  -- Three chunks whose concatenation we can verify.
  let chunks  := #["alpha".toUTF8, "beta".toUTF8, "gamma".toUTF8]
  let expected := "alphabetagamma"
  let total    := expected.length

  let server ← Server.mk serverCtx
  server.bind addr
  server.listen 128

  let srvTask ← (do
    let conn ← server.accept
    let mut buf := ByteArray.empty
    while buf.size < total do
      let chunk ← conn.recv? total.toUInt64
      buf := buf ++ chunk.getD ByteArray.empty
    conn.send buf
    Async.ofPromise conn.native.shutdown
  : Async Unit).toIO

  let cliTask ← (do
    let client ← Client.mk clientCtx (some "localhost")
    client.connect addr
    client.sendAll chunks
    let mut buf := ByteArray.empty
    while buf.size < total do
      let chunk ← client.recv? total.toUInt64
      buf := buf ++ chunk.getD ByteArray.empty
    assertEqStr (String.fromUTF8! buf) expected
    Async.ofPromise client.native.shutdown
  : Async Unit).toIO

  srvTask.block
  cliTask.block

def testSequentialConnections (addr : SocketAddress) (certFile keyFile : String) : IO Unit := do
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false

  let server ← Server.mk serverCtx
  server.bind addr
  server.listen 128

  for i in List.range 3 do
    let srvTask ← (do
      let conn ← server.accept
      let msg ← conn.recv? 1024
      conn.send (msg.getD ByteArray.empty)
      Async.ofPromise conn.native.shutdown
    : Async Unit).toIO

    let cliTask ← (do
      let client ← Client.mk clientCtx (some "localhost")
      client.connect addr
      let payload := s!"conn-{i}".toUTF8
      client.send payload
      let resp ← client.recv? 1024
      let got := String.fromUTF8! (resp.getD ByteArray.empty)
      unless got == s!"conn-{i}" do
        throw <| IO.userError s!"connection {i} echo mismatch: '{got}'"
      Async.ofPromise client.native.shutdown
    : Async Unit).toIO

    srvTask.block
    cliTask.block

def testBidirectional (addr : SocketAddress) (certFile keyFile : String) : IO Unit := do
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false

  let server ← Server.mk serverCtx
  server.bind addr
  server.listen 128

  let srvTask ← (do
    let conn ← server.accept
    conn.send "from-server".toUTF8        -- send without waiting for client first
    let msg ← conn.recv? 1024
    let got := String.fromUTF8! (msg.getD ByteArray.empty)
    unless got == "from-client" do
      throw <| IO.userError s!"server recv mismatch: '{got}'"
    Async.ofPromise conn.native.shutdown
  : Async Unit).toIO

  let cliTask ← (do
    let client ← Client.mk clientCtx (some "localhost")
    client.connect addr
    client.send "from-client".toUTF8      -- send without waiting for server first
    let msg ← client.recv? 1024
    let got := String.fromUTF8! (msg.getD ByteArray.empty)
    unless got == "from-server" do
      throw <| IO.userError s!"client recv mismatch: '{got}'"
    Async.ofPromise client.native.shutdown
  : Async Unit).toIO

  srvTask.block
  cliTask.block

def testZeroByteSend (addr : SocketAddress) (certFile keyFile : String) : IO Unit := do
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false

  let server ← Server.mk serverCtx
  server.bind addr
  server.listen 128

  let srvTask ← (do
    let conn ← server.accept
    -- Zero-byte send before and after a real message must not corrupt framing.
    conn.send ByteArray.empty
    conn.send "real".toUTF8
    conn.send ByteArray.empty
    Async.ofPromise conn.native.shutdown
  : Async Unit).toIO

  let cliTask ← (do
    let client ← Client.mk clientCtx (some "localhost")
    client.connect addr
    -- The real message must still arrive intact.
    let resp ← client.recv? 1024
    let got := String.fromUTF8! (resp.getD ByteArray.empty)
    unless got == "real" do
      throw <| IO.userError s!"zero-byte send: expected 'real', got '{got}'"
    Async.ofPromise client.native.shutdown
  : Async Unit).toIO

  srvTask.block
  cliTask.block

def testSendAllEmpty (addr : SocketAddress) (certFile keyFile : String) : IO Unit := do
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false

  let server ← Server.mk serverCtx
  server.bind addr
  server.listen 128

  let srvTask ← (do
    let conn ← server.accept
    let msg ← conn.recv? 1024
    conn.send (msg.getD ByteArray.empty)
    Async.ofPromise conn.native.shutdown
  : Async Unit).toIO

  let cliTask ← (do
    let client ← Client.mk clientCtx (some "localhost")
    client.connect addr
    client.sendAll #[]          -- empty array: should be a no-op
    client.send "after-empty".toUTF8
    let resp ← client.recv? 1024
    let got := String.fromUTF8! (resp.getD ByteArray.empty)
    unless got == "after-empty" do
      throw <| IO.userError s!"sendAll empty: expected 'after-empty', got '{got}'"
    Async.ofPromise client.native.shutdown
  : Async Unit).toIO

  srvTask.block
  cliTask.block

def testManySmallMessages (addr : SocketAddress) (certFile keyFile : String) : IO Unit := do
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false

  let n := 50
  let server ← Server.mk serverCtx
  server.bind addr
  server.listen 128

  let srvTask ← (do
    let conn ← server.accept
    -- Accumulate all n bytes.
    let mut buf := ByteArray.empty
    while buf.size < n do
      let chunk ← conn.recv? (n - buf.size).toUInt64
      buf := buf ++ chunk.getD ByteArray.empty
    conn.send buf
    Async.ofPromise conn.native.shutdown
  : Async Unit).toIO

  let cliTask ← (do
    let client ← Client.mk clientCtx (some "localhost")
    client.connect addr
    -- Send n individual one-byte messages.
    for i in List.range n do
      client.send (ByteArray.mk #[i.toUInt8])
    -- Receive all n bytes back.
    let mut buf := ByteArray.empty
    while buf.size < n do
      let chunk ← client.recv? (n - buf.size).toUInt64
      buf := buf ++ chunk.getD ByteArray.empty
    unless buf.size == n do
      throw <| IO.userError s!"many small messages: expected {n} bytes, got {buf.size}"
    for i in List.range n do
      unless buf[i]! == i.toUInt8 do
        throw <| IO.userError s!"many small messages: byte {i} mismatch"
    Async.ofPromise client.native.shutdown
  : Async Unit).toIO

  srvTask.block
  cliTask.block

def testSendWithTimeout (addr : SocketAddress) (certFile keyFile : String) : IO Unit := do
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false

  let server ← Server.mk serverCtx
  server.bind addr
  server.listen 128

  let srvTask ← (do
    let conn ← server.accept
    let msg ← conn.recv? 1024
    -- Echo with a generous send timeout; the happy path must not time out.
    conn.send (msg.getD ByteArray.empty) (timeout := some (.ofInt 5000))
    Async.ofPromise conn.native.shutdown
  : Async Unit).toIO

  let cliTask ← (do
    let client ← Client.mk clientCtx (some "localhost")
    client.connect addr
    -- A send and a sendAll, both with a generous timeout that should never fire.
    client.send "timed".toUTF8 (timeout := some (.ofInt 5000))
    let resp ← client.recv? 1024
    let got := String.fromUTF8! (resp.getD ByteArray.empty)
    unless got == "timed" do
      throw <| IO.userError s!"send-with-timeout mismatch: '{got}'"
    Async.ofPromise client.native.shutdown
  : Async Unit).toIO

  srvTask.block
  cliTask.block

#eval do
  let (certFile, keyFile) ← setupTestCerts
  testTCPSSL (SocketAddressV4.mk (.ofParts 127 0 0 1) 18443) certFile keyFile

#eval do
  let (certFile, keyFile) ← setupTestCerts
  testTCPSSL (SocketAddressV6.mk (.ofParts 0 0 0 0 0 0 0 1) 18444) certFile keyFile

#eval do
  let (certFile, keyFile) ← setupTestCerts
  testMultipleRoundTrips (SocketAddressV4.mk (.ofParts 127 0 0 1) 18445) certFile keyFile

#eval do
  let (certFile, keyFile) ← setupTestCerts
  testLargePayload (SocketAddressV4.mk (.ofParts 127 0 0 1) 18446) certFile keyFile

#eval do
  let (certFile, keyFile) ← setupTestCerts
  testSendAll (SocketAddressV4.mk (.ofParts 127 0 0 1) 18449) certFile keyFile

#eval do
  let (certFile, keyFile) ← setupTestCerts
  testSequentialConnections (SocketAddressV4.mk (.ofParts 127 0 0 1) 18451) certFile keyFile

#eval do
  let (certFile, keyFile) ← setupTestCerts
  testBidirectional (SocketAddressV4.mk (.ofParts 127 0 0 1) 18452) certFile keyFile

#eval do
  let (certFile, keyFile) ← setupTestCerts
  testZeroByteSend (SocketAddressV4.mk (.ofParts 127 0 0 1) 18454) certFile keyFile

#eval do
  let (certFile, keyFile) ← setupTestCerts
  testSendAllEmpty (SocketAddressV4.mk (.ofParts 127 0 0 1) 18457) certFile keyFile

#eval do
  let (certFile, keyFile) ← setupTestCerts
  testManySmallMessages (SocketAddressV4.mk (.ofParts 127 0 0 1) 18458) certFile keyFile

#eval do
  let (certFile, keyFile) ← setupTestCerts
  testSendWithTimeout (SocketAddressV4.mk (.ofParts 127 0 0 1) 18473) certFile keyFile
