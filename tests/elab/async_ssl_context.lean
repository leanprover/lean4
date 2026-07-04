import Std.Internal.SSL

/-!
Tests for `Std.Internal.SSL.Context`: TLS context creation and configuration.

This is the Context-only layer split out of #13112 (`TCP.SSL`); session and socket
behaviour are exercised in separate test files.
-/

open Std.Internal.SSL

-- A self-signed `CN=localhost` certificate and its matching RSA private key, embedded so the tests
-- neither shell out to `openssl` nor depend on it being installed. Valid until 2126; the smoke tests
-- only load these into a context (no handshake), so expiry is never checked. To regenerate:
--   openssl genrsa -out key.pem 2048
--   openssl req -new -x509 -key key.pem -out cert.pem -days 36500 -subj "/CN=localhost"

def testCertPEM : String :=
"-----BEGIN CERTIFICATE-----
MIIDCzCCAfOgAwIBAgIUfBsMFFfMmVyfKr1HjIF9ZUsOz0MwDQYJKoZIhvcNAQEL
BQAwFDESMBAGA1UEAwwJbG9jYWxob3N0MCAXDTI2MDcwNDE1NDQyNVoYDzIxMjYw
NjEwMTU0NDI1WjAUMRIwEAYDVQQDDAlsb2NhbGhvc3QwggEiMA0GCSqGSIb3DQEB
AQUAA4IBDwAwggEKAoIBAQC7SwGfQ+WLyJwnRlX37WMUEDT/YVZd0PV/6PPJSFx3
0z2vZnqMh9S7gQPvkYkon7qMtqF5jlJt3zDmddjuhhwHqeNj1htKnWPjhh8rc2DG
7v9u/36O92fz2jKUn8qHGG80+SiW4LkE8uXuC/ia0a1W03iT7rApICuSIgNrP5Zr
XZ3pHxn4m7GxnOxm/5jt0SX3HQkRV+VMEo0cGEq/8ZvmwnOOG14C/o/FxFw9zxw8
pDTabvfLVxoHCMOu7UB3c0Hg6SzM8cD/QefWQRLyD/rZIw34GcTs9IklWxJ0loqj
Y1q0c5p5991zRC2SqmM6vpAjc6dpijIAZvsycewlnY1bAgMBAAGjUzBRMB0GA1Ud
DgQWBBRam+qywW30FsQlhzW2SV7dHs96NDAfBgNVHSMEGDAWgBRam+qywW30FsQl
hzW2SV7dHs96NDAPBgNVHRMBAf8EBTADAQH/MA0GCSqGSIb3DQEBCwUAA4IBAQC7
ItNAWGWOQDfjSCi2XqbKPSMbo3d8x2fQclYuFXu3QjbsmTrkzCehvGAyXHUtbnwa
wAufdEDKjfmUZmquVQd54oTCDgNtDF4729kD7pBeIIyhWyH0osPAs9mva37ripqC
MQ3kMClzS8FSBhB03CSdkypzx0znI2rIcxbMDPCIoYtkKYyvc6/yztWZfVbhHWPC
6bYAHOFpqFCOSzcZFwzWjWmAnH+pPEX8khDTTY676VG/Yuy2F/BgCdXco8VE+kiW
hh/mZMXyGuGKuYexz8Tv5M3qzdqxNmhFObyJPk/Y7XgIoBtdyHLMkqYN5fnlUMtQ
gjuJv2wDBVKza1YhNdr1
-----END CERTIFICATE-----
"

def testKeyPEM : String :=
"-----BEGIN PRIVATE KEY-----
MIIEvQIBADANBgkqhkiG9w0BAQEFAASCBKcwggSjAgEAAoIBAQC7SwGfQ+WLyJwn
RlX37WMUEDT/YVZd0PV/6PPJSFx30z2vZnqMh9S7gQPvkYkon7qMtqF5jlJt3zDm
ddjuhhwHqeNj1htKnWPjhh8rc2DG7v9u/36O92fz2jKUn8qHGG80+SiW4LkE8uXu
C/ia0a1W03iT7rApICuSIgNrP5ZrXZ3pHxn4m7GxnOxm/5jt0SX3HQkRV+VMEo0c
GEq/8ZvmwnOOG14C/o/FxFw9zxw8pDTabvfLVxoHCMOu7UB3c0Hg6SzM8cD/QefW
QRLyD/rZIw34GcTs9IklWxJ0loqjY1q0c5p5991zRC2SqmM6vpAjc6dpijIAZvsy
cewlnY1bAgMBAAECggEADV4RnBHnAL6NMpppCVx2jViIx89lMCX5V6tDNxMEkoLP
rMSmK4CIVOek5cTf4rffwypHxRq81F2xKkmv9Xo55uwfsCD4aq9oETWh5OKDvj8R
mRUALekHkNZ6dLQg6tp6GXBNDtO0MN+7PG27TSV49zD5sqk/Bnhm07O8xbtQm5IA
LheZd4GPqBdTIf1krFNP86Th4X+DKrnuNmiXS4lDuhH/rheRfTQ4VK/srnrj//Zw
I+AeXwnch25CByXp+CoSHpwZGPYzfknZBjmkh1QbwMR/ivjA954BxbVsWl+/cAYh
7+MEvkrInJYqbwSVWQrVrKjRuHqI0OcvymBbGXoaHQKBgQDg+HBLB0Tt+mQqX+Kb
eo0ymK+V2Y0kprlVthTHPJHpA+zMcEBJWjlz0IpdfkjKAMrVoVJB4Fn8Y4Wj4Nzq
yV1AsZ/cHsH3NWnwiMaRvVTs7O60Vhs0G/I2lIx6T0dl4qWFjJQizrvMctNFVkvR
rh4tnGQnTMBViqKAB5CiW/o/dwKBgQDVIDNchhEAijUNJ60c4XcbrhGjlBmjDRyG
KfVM1LMQz9u20bZvOP/qL5wNHrlGqplOBUvD1o/J6b4ZIgzhWNB0WrPrBBi40pvv
9v7wCTZ3XfJ+KrGlWOfB0fPVs2kKjLd8b+1xoa7JM/RJIBmytXj3o9lS/6F7SkjH
0EQv086CPQKBgE83jCsPOzllMwIs01mWNMP9Oc7VVTrzrk09GWHytRpM9IQkfq6V
o6dhZmd3gWAIGWRSMunZezZBQRysoH3YPAr8wOK8veYzm8NEFk/ZUF9BKui7bUbT
FF4dvr2OzwBUZ554Gu2KyFw8jqJaucXyvtOmvymLgCpe78uPXmGda6gPAoGBAL3y
5xPtgTXD+ChzVjzJTkjjSWFLW9YQl32T48bIQ5gWSbKVEk3qtVvZdvHSkjrDTcNV
wQMYNis1InJwAJ7Pc2pgdL5fdlEzlDu5Hdp9u4eDud5s2suNg3EhWHr8XgBDDj3f
2/ZMreUxYuXRsFWwm9HKvKTWpOund1pu6nbeBc3ZAoGAWKJkhw7KoELqiCpTn3If
7ZN64vgqkNacXfjzc4D5oJ2aqAPJsTBdJ14+VShecgc5Kn0QriP0mTU712/GiK08
A0Xb02+1ouerqiUE+Ea++rZphkyC0g+MKcoCWFWKDmtJuC7vtCGLOeFuLgHahqqS
yIGPWTqB+JUmYpWBWIvu0Gg=
-----END PRIVATE KEY-----
"

-- Writes the embedded certificate and key to a temporary directory, returning their paths.
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
