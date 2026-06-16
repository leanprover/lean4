import Std.Internal.SSL

/-!
Tests for `Std.Internal.SSL.Context`: TLS context creation and configuration.

This is the Context-only layer split out of #13112 (`TCP.SSL`); session and socket
behaviour are exercised in separate test files.
-/

open Std.Internal.SSL

-- Generate a self-signed certificate for testing (cached: skips generation if files exist).
def setupTestCerts : IO (String × String) := do
  IO.FS.createDirAll "/tmp/lean_ssl_test"
  let keyFile  := "/tmp/lean_ssl_test/key.pem"
  let certFile := "/tmp/lean_ssl_test/cert.pem"

  let keyExists  ← System.FilePath.pathExists keyFile
  let certExists ← System.FilePath.pathExists certFile
  unless keyExists && certExists do
    discard <| IO.Process.output {
      cmd  := "openssl"
      args := #["genrsa", "-out", keyFile, "2048"]
    }
    discard <| IO.Process.output {
      cmd  := "openssl"
      args := #["req", "-new", "-x509", "-key", keyFile, "-out", certFile, "-days", "1", "-subj", "/CN=localhost"]
    }

  return (certFile, keyFile)

-- Context creation and configuration (smoke test).
def testContextCreation (certFile keyFile : String) : IO Unit := do
  let serverCtx ← Context.Server.mk
  serverCtx.configure certFile keyFile

  let clientCtx ← Context.Client.mk
  clientCtx.configure "" false

  -- Configuring with a CA file path (non-empty) exercises the other branch.
  let clientCtx2 ← Context.Client.mk
  clientCtx2.configure certFile false

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
