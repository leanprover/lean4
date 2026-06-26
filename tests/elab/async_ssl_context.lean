import Std.Internal.SSL

/-!
Tests for `Std.Internal.SSL.Context`: TLS context creation and configuration.

This is the Context-only layer split out of #13112 (`TCP.SSL`); session and socket
behaviour are exercised in separate test files.
-/

open Std.Internal.SSL

-- Generates a fresh self-signed certificate in a temporary directory for testing.
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

-- Context creation and configuration (smoke test).
def testContextCreation (certFile keyFile : String) : IO Unit := do
  let serverCtx ← Context.Server.mk
  serverCtx.configure certFile keyFile

  -- Empty CA with `verifyPeer := false` disables verification without parsing any CA material.
  let clientCtx ← Context.Client.mk
  clientCtx.configure "" false

  -- Non-empty CA file with `verifyPeer := true` exercises the additive trust path: the system
  -- roots plus the supplied CA (via `SSL_CTX_load_verify_locations`).
  let clientCtx2 ← Context.Client.mk
  clientCtx2.configure certFile true

  -- A non-empty CA path with `verifyPeer := false` is accepted, but the CA file is not parsed.
  let clientCtx3 ← Context.Client.mk
  clientCtx3.configure certFile false

-- Configuring a client from an in-memory PEM string.
def testConfigureClientFromPEM (certFile : String) : IO Unit := do
  let caPEM ← IO.FS.readFile certFile
  let clientCtx ← Context.Client.mk
  clientCtx.configureFromPEM caPEM true

-- Asserts that an IO action fails, used to exercise the rejection/error paths.
def assertThrows (label : String) (act : IO Unit) : IO Unit := do
  match ← act.toBaseIO with
  | .ok _ => throw <| IO.userError s!"{label}: expected failure, but it succeeded"
  | .error _ => pure ()

-- An empty CA bundle with `verifyPeer := true` falls back to the platform trust anchors and succeeds.
def testConfigureFromPEMEmptyFallsBack : IO Unit := do
  let clientCtx ← Context.Client.mk
  clientCtx.configureFromPEM "" true

-- `verifyPeer := false` succeeds without parsing the CA material, even for a real bundle.
def testConfigureFromPEMNoVerify (certFile : String) : IO Unit := do
  let caPEM ← IO.FS.readFile certFile
  let clientCtx ← Context.Client.mk
  clientCtx.configureFromPEM caPEM false

-- Malformed PEM input is rejected rather than silently ignored.
def testConfigureFromPEMRejectsGarbage : IO Unit := do
  let clientCtx ← Context.Client.mk
  assertThrows "garbage PEM" (clientCtx.configureFromPEM "not a certificate at all" true)

-- A well-formed PEM block that contains no certificate is rejected.
def testConfigureFromPEMRejectsEmptyBlock : IO Unit := do
  let clientCtx ← Context.Client.mk
  assertThrows "PEM without certificates"
    (clientCtx.configureFromPEM "-----BEGIN CERTIFICATE-----\n-----END CERTIFICATE-----\n" true)

-- A non-existent CA file with `verifyPeer := true` is rejected (the file-based additive path fails).
def testConfigureRejectsMissingCAFile : IO Unit := do
  let clientCtx ← Context.Client.mk
  assertThrows "missing CA file"
    (clientCtx.configure "/nonexistent/path/to/ca.pem" true)

#eval do
  let (certFile, keyFile) ← setupTestCerts
  testContextCreation certFile keyFile

#eval do
  let (certFile, _) ← setupTestCerts
  testConfigureClientFromPEM certFile

#eval testConfigureFromPEMEmptyFallsBack

#eval do
  let (certFile, _) ← setupTestCerts
  testConfigureFromPEMNoVerify certFile

#eval testConfigureFromPEMRejectsGarbage

#eval testConfigureFromPEMRejectsEmptyBlock

#eval testConfigureRejectsMissingCAFile
