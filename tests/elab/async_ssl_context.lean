import Std.Internal.SSL
import Lean

/-!
Tests for `Std.Internal.SSL.Context`: TLS context creation and configuration.

This is the Context-only layer split out of #13112 (`TCP.SSL`); session and socket
behaviour are exercised in separate test files.
-/

open Std.Internal.SSL

open Lean in

elab "include_cert% " path:str : term => do
  let dir := (System.FilePath.mk (← readThe Core.Context).fileName).parent.getD ⟨"."⟩
  return mkStrLit (← IO.FS.readFile (dir / path.getString))

def testCertPEM : String := include_cert% "async_ssl_certs/cert.pem"
def testKeyPEM : String := include_cert% "async_ssl_certs/key.pem"

-- Writes the embedded certificate and key to a temporary directory for the path-based APIs.
def setupTestCerts : IO (String × String) := do
  let dir ← IO.FS.createTempDir
  let keyFile  := toString (dir / "key.pem")
  let certFile := toString (dir / "cert.pem")
  IO.FS.writeFile keyFile testKeyPEM
  IO.FS.writeFile certFile testCertPEM
  return (certFile, keyFile)

-- Context creation and configuration (smoke test).
def testContextCreation (certFile keyFile : String) : IO Unit := do
  let _serverCtx ← Context.Server.mk certFile keyFile

  -- Empty CA with `verifyPeer := false` disables verification without parsing any CA material.
  let _clientCtx ← Context.Client.mk "" false

  -- Non-empty CA file with `verifyPeer := true` exercises the additive trust path: the system
  -- roots plus the supplied CA (via `SSL_CTX_load_verify_locations`).
  let _clientCtx2 ← Context.Client.mk certFile true

  -- A non-empty CA path with `verifyPeer := false` is accepted, but the CA file is not parsed.
  let _clientCtx3 ← Context.Client.mk certFile false

  -- Defaults: no CA file, peer verification against the system trust anchors.
  let _clientCtx4 ← Context.Client.mk

-- Creating a client from an in-memory PEM string.
def testMkClientFromPEM (certFile : String) : IO Unit := do
  let caPEM ← IO.FS.readFile certFile
  let _clientCtx ← Context.Client.mkFromPEM caPEM true

-- Asserts that an IO action fails, used to exercise the rejection/error paths.
def assertThrows (label : String) (act : IO Unit) : IO Unit := do
  match ← act.toBaseIO with
  | .ok _ => throw <| IO.userError s!"{label}: expected failure, but it succeeded"
  | .error _ => pure ()

-- An empty CA bundle with `verifyPeer := true` falls back to the platform trust anchors and succeeds.
def testMkFromPEMEmptyFallsBack : IO Unit := do
  let _clientCtx ← Context.Client.mkFromPEM "" true

-- `verifyPeer := false` succeeds without parsing the CA material, even for a real bundle.
def testMkFromPEMNoVerify (certFile : String) : IO Unit := do
  let caPEM ← IO.FS.readFile certFile
  let _clientCtx ← Context.Client.mkFromPEM caPEM false

-- Malformed PEM input is rejected rather than silently ignored.
def testMkFromPEMRejectsGarbage : IO Unit := do
  assertThrows "garbage PEM"
    (discard <| Context.Client.mkFromPEM "not a certificate at all" true)

-- A well-formed PEM block that contains no certificate is rejected.
def testMkFromPEMRejectsEmptyBlock : IO Unit := do
  assertThrows "PEM without certificates"
    (discard <| Context.Client.mkFromPEM "-----BEGIN CERTIFICATE-----\n-----END CERTIFICATE-----\n" true)

-- A non-existent CA file with `verifyPeer := true` is rejected (the file-based additive path fails).
def testMkRejectsMissingCAFile : IO Unit := do
  assertThrows "missing CA file"
    (discard <| Context.Client.mk "/nonexistent/path/to/ca.pem" true)

-- A server context with non-existent certificate/key files is rejected.
def testMkServerRejectsMissingFiles : IO Unit := do
  assertThrows "missing server cert"
    (discard <| Context.Server.mk "/nonexistent/cert.pem" "/nonexistent/key.pem")

-- A server context whose certificate and key do not match is rejected (here by swapping the file
-- arguments so neither parses as the expected PEM object).
def testMkServerRejectsSwappedFiles (certFile keyFile : String) : IO Unit := do
  assertThrows "swapped server cert/key"
    (discard <| Context.Server.mk keyFile certFile)

#eval do
  let (certFile, keyFile) ← setupTestCerts
  testContextCreation certFile keyFile

#eval do
  let (certFile, _) ← setupTestCerts
  testMkClientFromPEM certFile

#eval testMkFromPEMEmptyFallsBack

#eval do
  let (certFile, _) ← setupTestCerts
  testMkFromPEMNoVerify certFile

#eval testMkFromPEMRejectsGarbage

#eval testMkFromPEMRejectsEmptyBlock

#eval testMkRejectsMissingCAFile

#eval testMkServerRejectsMissingFiles

#eval do
  let (certFile, keyFile) ← setupTestCerts
  testMkServerRejectsSwappedFiles certFile keyFile
