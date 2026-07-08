import Std.Async.TCP.SSL
import Std.Net.Addr

/-!
Tests for `Std.Async.TCP.SSL`: certificate verification, SNI/hostname matching, SAN, and expiry.
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

def setupWildcardCert (keyFile : String) : IO String := do
  let dir ← IO.FS.createTempDir
  let certFile := toString (dir / "wildcard_cert.pem")
  let out ← IO.Process.output {
    cmd  := "openssl"
    args := #["req", "-new", "-x509", "-key", keyFile, "-out", certFile, "-days", "1",
              "-subj", "/CN=*.test.local",
              "-addext", "subjectAltName=DNS:*.test.local,DNS:test.local"]
  }
  unless out.exitCode == 0 do
    throw <| IO.userError s!"openssl wildcard cert failed: {out.stderr}"
  return certFile

def setupMultiSANCert (keyFile : String) : IO String := do
  let dir ← IO.FS.createTempDir
  let certFile := toString (dir / "multisan_cert.pem")
  let out ← IO.Process.output {
    cmd  := "openssl"
    args := #["req", "-new", "-x509", "-key", keyFile, "-out", certFile, "-days", "1",
              "-subj", "/CN=alpha.test.local",
              "-addext", "subjectAltName=DNS:alpha.test.local,DNS:beta.test.local"]
  }
  unless out.exitCode == 0 do
    throw <| IO.userError s!"openssl multi-SAN cert failed: {out.stderr}"
  return certFile

def setupExpiredCert (keyFile : String) : IO String := do
  let dir ← IO.FS.createTempDir
  let csrFile  := toString (dir / "expired_csr.pem")
  let certFile := toString (dir / "expired_cert.pem")
  let csrOut ← IO.Process.output {
    cmd  := "openssl"
    args := #["req", "-new", "-key", keyFile, "-out", csrFile, "-subj", "/CN=localhost"]
  }
  unless csrOut.exitCode == 0 do
    throw <| IO.userError s!"openssl expired cert CSR failed: {csrOut.stderr}"
  let certOut ← IO.Process.output {
    cmd  := "openssl"
    args := #["x509", "-req", "-in", csrFile, "-signkey", keyFile,
              "-out", certFile, "-set_serial", "99",
              "-not_before", "20200101000000Z", "-not_after", "20200102000000Z"]
  }
  unless certOut.exitCode == 0 do
    throw <| IO.userError s!"openssl expired cert failed: {certOut.stderr}"
  return certFile

def testHostnameMismatchFails (addr : SocketAddress) (certFile keyFile : String) : IO Unit := do
  let serverCtx ← Context.Server.mk certFile keyFile

  let clientCtx ← Context.Client.mk certFile true   -- our self-signed cert as CA; chain verifies

  let server ← Server.mk serverCtx
  server.bind addr
  server.listen 128

  let srvTask ← (do
    try
      let conn ← server.accept
      conn.tlsShutdown
    catch _ => pure ()
  : Async Unit).toIO

  let cliTask ← (do
    let client ← Client.mk clientCtx (some "evil.example.com")
    let handshakeFailed ← try
      client.connect addr
      pure false
    catch _ =>
      pure true
    unless handshakeFailed do
      throw <| IO.userError
        "testHostnameMismatchFails: handshake succeeded for a mismatched hostname"

    let rejectedAsBroken ← try
      client.send "must-not-send".toUTF8
      pure false
    catch e =>
      pure (toString e == "TLS connection is in a broken state")
    unless rejectedAsBroken do
      throw <| IO.userError
        "testHostnameMismatchFails: failed handshake did not mark the connection broken"
  : Async Unit).toIO

  cliTask.block
  try srvTask.block catch _ => pure ()

def testDefaultVerifiesPeer (addr : SocketAddress) (certFile keyFile : String) : IO Unit := do
  let serverCtx ← Context.Server.mk certFile keyFile

  -- Deliberately rely on the `mk` defaults (no CA file, peer verification on).
  let clientCtx ← Context.Client.mk

  let server ← Server.mk serverCtx
  server.bind addr
  server.listen 128

  let srvTask ← (do
    try
      let conn ← server.accept
      conn.tlsShutdown
    catch _ => pure ()
  : Async Unit).toIO

  let connectSucceeded ← IO.mkRef false

  let cliTask ← (do
    let client ← Client.mk clientCtx (some "localhost")
    client.connect addr
    connectSucceeded.set true
    client.tlsShutdown
  : Async Unit).toIO

  try cliTask.block catch _ => pure ()
  try srvTask.block catch _ => pure ()

  if ← connectSucceeded.get then
    throw <| IO.userError
      "testDefaultVerifiesPeer: handshake succeeded against a self-signed cert — \
       Context.Client.mk should default to SSL_VERIFY_PEER with system trust anchors"

def testVerifyResultValues (addrFail addrOk : SocketAddress) (certFile keyFile : String) : IO Unit := do
  -- Part 1: cert verification FAILURE — code must be > 0.
  do
    let serverCtx ← Context.Server.mk certFile keyFile
    let clientCtx ← Context.Client.mk "" true   -- system anchors; self-signed cert is NOT trusted

    let server ← Server.mk serverCtx
    server.bind addrFail
    server.listen 128

    let srvTask ← (do
      try
        let conn ← server.accept
        (try conn.tlsShutdown catch _ => pure ())
      catch _ => pure ()
    : Async Unit).toIO

    let cliTask ← (do
      let client ← Client.mk clientCtx (some "localhost")
      try client.connect addrFail catch _ => pure ()
      let code ← client.verifyResult
      let msg  ← client.verifyResultString
      if code == 0 then
        throw <| IO.userError
          s!"testVerifyResultValues failure path: got code=0 (X509_V_OK) after a \
             handshake that should have failed certificate verification"
      if msg.isEmpty then
        throw <| IO.userError
          s!"testVerifyResultValues: verifyResultString empty for code={code}"
      if msg == "ok" then
        throw <| IO.userError
          s!"testVerifyResultValues: code={code} but string is 'ok' (mismatch)"
    : Async Unit).toIO

    srvTask.block
    cliTask.block

  -- Part 2: cert verification SUCCESS — code must be 0.
  do
    let serverCtx ← Context.Server.mk certFile keyFile
    let clientCtx ← Context.Client.mk certFile true   -- use the cert itself as the trust anchor

    let server ← Server.mk serverCtx
    server.bind addrOk
    server.listen 128

    let srvTask ← (do
      let conn ← server.accept
      conn.tlsShutdown
    : Async Unit).toIO

    let cliTask ← (do
      let client ← Client.mk clientCtx (some "localhost")
      client.connect addrOk
      let code ← client.verifyResult
      let msg  ← client.verifyResultString
      if code != 0 then
        throw <| IO.userError
          s!"testVerifyResultValues success path: got code={code} (expected 0 / X509_V_OK), msg='{msg}'"
      if msg != "ok" then
        throw <| IO.userError
          s!"testVerifyResultValues: code=0 but string is '{msg}', expected 'ok'"
      client.tlsShutdown
    : Async Unit).toIO

    srvTask.block
    cliTask.block

def testWildcardSAN (addrOk addrFail : SocketAddress) (wildcardCert keyFile : String) :
    IO Unit := do
  let serverCtx ← Context.Server.mk wildcardCert keyFile

  -- Client context trusts the wildcard cert as its only CA.
  let clientCtxOk ← Context.Client.mk wildcardCert true
  let clientCtxFail ← Context.Client.mk wildcardCert true

  -- Part A: sub.test.local should match *.test.local → handshake succeeds.
  let serverA ← Server.mk serverCtx
  serverA.bind addrOk
  serverA.listen 128

  let srvA ← (do discard <| serverA.accept : Async Unit).toIO
  let cliA ← (do
    let client ← Client.mk clientCtxOk (some "sub.test.local")
    client.connect addrOk
  : Async Unit).toIO
  srvA.block
  cliA.block

  -- Part B: sub.other.local should NOT match *.test.local → handshake fails.
  let serverB ← Server.mk serverCtx
  serverB.bind addrFail
  serverB.listen 128

  let srvB ← (do
    try discard <| serverB.accept
    catch _ => pure ()
  : Async Unit).toIO
  let cliB ← (do
    let client ← Client.mk clientCtxFail (some "sub.other.local")
    let threw ← try
      client.connect addrFail
      pure false
    catch _ =>
      pure true
    unless threw do
      throw <| IO.userError
        "testWildcardSAN: handshake succeeded for sub.other.local — wildcard mismatch not detected"
  : Async Unit).toIO
  srvB.block
  cliB.block

def testMultiSAN (addrAlpha addrBeta addrGamma : SocketAddress)
    (multiCert keyFile : String) : IO Unit := do
  let serverCtx ← Context.Server.mk multiCert keyFile

  let mkClient : IO Context.Client := do
    let ctx ← Context.Client.mk multiCert true
    return ctx

  -- alpha.test.local → matches first SAN → success.
  let serverAlpha ← Server.mk serverCtx
  serverAlpha.bind addrAlpha
  serverAlpha.listen 128
  let srvAlpha ← (do discard <| serverAlpha.accept : Async Unit).toIO
  let cliAlpha ← (do
    let client ← Client.mk (← mkClient) (some "alpha.test.local")
    client.connect addrAlpha
  : Async Unit).toIO
  srvAlpha.block
  cliAlpha.block

  -- beta.test.local → matches second SAN → success.
  let serverBeta ← Server.mk serverCtx
  serverBeta.bind addrBeta
  serverBeta.listen 128
  let srvBeta ← (do discard <| serverBeta.accept : Async Unit).toIO
  let cliBeta ← (do
    let client ← Client.mk (← mkClient) (some "beta.test.local")
    client.connect addrBeta
  : Async Unit).toIO
  srvBeta.block
  cliBeta.block

  -- gamma.test.local → not in SAN list → fail.
  let serverGamma ← Server.mk serverCtx
  serverGamma.bind addrGamma
  serverGamma.listen 128
  let srvGamma ← (do
    try discard <| serverGamma.accept
    catch _ => pure ()
  : Async Unit).toIO
  let cliGamma ← (do
    let client ← Client.mk (← mkClient) (some "gamma.test.local")
    let threw ← try
      client.connect addrGamma
      pure false
    catch _ =>
      pure true
    unless threw do
      throw <| IO.userError
        "testMultiSAN: handshake succeeded for gamma.test.local — SAN mismatch not detected"
  : Async Unit).toIO
  srvGamma.block
  cliGamma.block

def testConcurrentContextReuse (addr : SocketAddress) (certFile keyFile : String) :
    IO Unit := do
  let serverCtx ← Context.Server.mk certFile keyFile
  let clientCtx ← Context.Client.mk certFile true

  let server ← Server.mk serverCtx
  server.bind addr
  server.listen 128

  let srvTask ← (do
    for _ in List.range 3 do
      let conn ← server.accept
      conn.send "hi".toUTF8
  : Async Unit).toIO

  -- Start all three client tasks before blocking on any, so the handshakes
  -- race concurrently and share the same SSL_CTX.
  let cli1 ← (do
    let client ← Client.mk clientCtx (some "localhost")
    client.connect addr
    discard <| client.recv? 1024
  : Async Unit).toIO
  let cli2 ← (do
    let client ← Client.mk clientCtx (some "localhost")
    client.connect addr
    discard <| client.recv? 1024
  : Async Unit).toIO
  let cli3 ← (do
    let client ← Client.mk clientCtx (some "localhost")
    client.connect addr
    discard <| client.recv? 1024
  : Async Unit).toIO

  srvTask.block
  cli1.block
  cli2.block
  cli3.block

def testExpiredCertRejected (addr : SocketAddress) (expiredCert keyFile : String) :
    IO Unit := do
  let serverCtx ← Context.Server.mk expiredCert keyFile
  -- The client trusts the expired cert as its only CA; the chain verifies but
  -- the validity period check must still fail.
  let clientCtx ← Context.Client.mk expiredCert true

  let server ← Server.mk serverCtx
  server.bind addr
  server.listen 128

  let srvTask ← (do
    try discard <| server.accept
    catch _ => pure ()
  : Async Unit).toIO

  let cliTask ← (do
    let client ← Client.mk clientCtx (some "localhost")
    let threw ← try
      client.connect addr
      pure false
    catch _ =>
      pure true
    unless threw do
      throw <| IO.userError
        "testExpiredCertRejected: handshake succeeded with an expired certificate"
  : Async Unit).toIO

  srvTask.block
  cliTask.block

#eval do
  let (certFile, keyFile) ← setupTestCerts
  testHostnameMismatchFails (SocketAddressV4.mk (.ofParts 127 0 0 1) 18461) certFile keyFile

#eval do
  let (certFile, keyFile) ← setupTestCerts
  testDefaultVerifiesPeer (SocketAddressV4.mk (.ofParts 127 0 0 1) 18462) certFile keyFile

#eval do
  let (certFile, keyFile) ← setupTestCerts
  testVerifyResultValues
    (SocketAddressV4.mk (.ofParts 127 0 0 1) 18463)
    (SocketAddressV4.mk (.ofParts 127 0 0 1) 18464)
    certFile keyFile

#eval do
  let (_, keyFile) ← setupTestCerts
  let wildcardCert ← setupWildcardCert keyFile
  testWildcardSAN
    (SocketAddressV4.mk (.ofParts 127 0 0 1) 18466)
    (SocketAddressV4.mk (.ofParts 127 0 0 1) 18467)
    wildcardCert keyFile

#eval do
  let (_, keyFile) ← setupTestCerts
  let multiCert ← setupMultiSANCert keyFile
  testMultiSAN
    (SocketAddressV4.mk (.ofParts 127 0 0 1) 18468)
    (SocketAddressV4.mk (.ofParts 127 0 0 1) 18469)
    (SocketAddressV4.mk (.ofParts 127 0 0 1) 18470)
    multiCert keyFile

#eval do
  let (certFile, keyFile) ← setupTestCerts
  testConcurrentContextReuse (SocketAddressV4.mk (.ofParts 127 0 0 1) 18471) certFile keyFile

#eval do
  let (_, keyFile) ← setupTestCerts
  let expiredCert ← setupExpiredCert keyFile
  testExpiredCertRejected (SocketAddressV4.mk (.ofParts 127 0 0 1) 18472) expiredCert keyFile
