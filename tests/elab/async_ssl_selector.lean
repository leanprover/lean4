import Std.Async.TCP.SSL
import Std.Net.Addr

/-!
Tests for `Std.Async.TCP.SSL`: `acceptSelector`/`recvSelector` and selector timeouts.
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

def testAcceptSelector (addr : SocketAddress) (certFile keyFile : String) : IO Unit := do
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false

  let server ← Server.mk serverCtx
  server.bind addr
  server.listen 128

  let srvTask ← (do
    let conn ← Selectable.one #[
      .case (selector := server.acceptSelector) (cont := fun c => return c)
    ]
    let msg ← conn.recv? 1024
    conn.send (msg.getD ByteArray.empty)
    Async.ofPromise conn.native.shutdown
  : Async Unit).toIO

  let cliTask ← (do
    let client ← Client.mk clientCtx (some "localhost")
    client.connect addr
    client.send "via selector".toUTF8
    let resp ← client.recv? 1024
    let got := String.fromUTF8! (resp.getD ByteArray.empty)
    unless got == "via selector" do
      throw <| IO.userError s!"selector round-trip mismatch: '{got}'"
    Async.ofPromise client.native.shutdown
  : Async Unit).toIO

  srvTask.block
  cliTask.block

def testRecvSelector (addr : SocketAddress) (certFile keyFile : String) : IO Unit := do
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false

  let server ← Server.mk serverCtx
  server.bind addr
  server.listen 128

  let srvTask ← (do
    let conn ← server.accept
    conn.send "pushed".toUTF8
    let ack ← conn.recv? 1024
    let got := String.fromUTF8! (ack.getD ByteArray.empty)
    unless got == "ack" do
      throw <| IO.userError s!"server: expected 'ack', got '{got}'"
    Async.ofPromise conn.native.shutdown
  : Async Unit).toIO

  let cliTask ← (do
    let client ← Client.mk clientCtx (some "localhost")
    client.connect addr
    -- Block until the server's push arrives, using recvSelector.
    let result ← Selectable.one #[
      .case (selector := client.recvSelector 1024) (cont := fun r => return r)
    ]
    let got := String.fromUTF8! (result.getD ByteArray.empty)
    unless got == "pushed" do
      throw <| IO.userError s!"recvSelector mismatch: '{got}'"
    client.send "ack".toUTF8
    Async.ofPromise client.native.shutdown
  : Async Unit).toIO

  srvTask.block
  cliTask.block

def testRecvSelectorWithTimeout (addr : SocketAddress) (certFile keyFile : String) : IO Unit := do
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false

  let server ← Server.mk serverCtx
  server.bind addr
  server.listen 128

  let srvTask ← (do
    let conn ← server.accept
    conn.send "selector-data".toUTF8
    conn.tlsShutdown
  : Async Unit).toIO

  let cliTask ← (do
    let client ← Client.mk clientCtx (some "localhost")
    client.connect addr

    let timeout ← Sleep.mk (Std.Time.Millisecond.Offset.ofInt 2000)
    let result ← Selectable.one #[
      .case (selector := client.recvSelector 1024) (cont := fun r => return (some r)),
      .case (selector := timeout.selector)         (cont := fun _ => return none)
    ]
    match result with
    | none =>
      throw <| IO.userError "recvSelectorWithTimeout: timed out after 2 s"
    | some resp =>
      let got := String.fromUTF8! (resp.getD ByteArray.empty)
      unless got == "selector-data" do
        throw <| IO.userError s!"recvSelectorWithTimeout: expected 'selector-data', got '{got}'"
    client.tlsShutdown
  : Async Unit).toIO

  srvTask.block
  cliTask.block

def testRecvTimeout (addr : SocketAddress) (certFile keyFile : String) : IO Unit := do
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk "" false

  let server ← Server.mk serverCtx
  server.bind addr
  server.listen 128

  let srvTask ← (do
    let conn ← server.accept
    -- Let the client's first receive time out, then prove that the same TLS
    -- session can still receive application data. The wide margin over the
    -- client's 500ms timeout keeps the test stable on loaded CI machines.
    Async.sleep 2000
    conn.send "after-timeout".toUTF8
    conn.tlsShutdown
  : Async Unit).toIO

  let cliTask ← (do
    let client ← Client.mk clientCtx (some "localhost")
    client.connect addr

    let mut timedOut := false
    try
      discard <| client.recv? 1024 (timeout := some (Std.Time.Millisecond.Offset.ofInt 500))
    catch e =>
      timedOut := true
      let msg := toString e
      unless msg == "TLS operation timed out" do
        throw <| IO.userError s!"recvTimeout: expected timeout error, got '{msg}'"
    unless timedOut do
      throw <| IO.userError "recvTimeout: recv? did not time out"

    let response ← client.recv? 1024
    let got := String.fromUTF8! (response.getD ByteArray.empty)
    unless got == "after-timeout" do
      throw <| IO.userError s!"recvTimeout: expected reusable connection, got '{got}'"
    client.tlsShutdown
  : Async Unit).toIO

  cliTask.block
  srvTask.block

#eval do
  let (certFile, keyFile) ← setupTestCerts
  testAcceptSelector (SocketAddressV4.mk (.ofParts 127 0 0 1) 18448) certFile keyFile

#eval do
  let (certFile, keyFile) ← setupTestCerts
  testRecvSelector (SocketAddressV4.mk (.ofParts 127 0 0 1) 18450) certFile keyFile

#eval do
  let (certFile, keyFile) ← setupTestCerts
  testRecvSelectorWithTimeout (SocketAddressV4.mk (.ofParts 127 0 0 1) 18460) certFile keyFile

#eval do
  let (certFile, keyFile) ← setupTestCerts
  testRecvTimeout (SocketAddressV4.mk (.ofParts 127 0 0 1) 18470) certFile keyFile
