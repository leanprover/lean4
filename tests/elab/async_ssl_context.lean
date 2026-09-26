import Std.Internal.SSL
import Std.Async.System
import Lean

/-!
Tests for `Std.Internal.SSL.Context` construction. Nothing here performs a handshake, so trust
decisions are only observable through the contexts that are refused.
-/

open Std.Internal.SSL

open Lean in

elab "include_cert% " path:str : term => do
  let dir := (System.FilePath.mk (← readThe Core.Context).fileName).parent.getD ⟨"."⟩
  return mkStrLit (← IO.FS.readFile (dir / path.getString))

def testCertPEM : String := include_cert% "async_ssl_certs/cert.pem"
def testKeyPEM : String := include_cert% "async_ssl_certs/key.pem"
def testWildcardCertPEM : String := include_cert% "async_ssl_certs/wildcard.pem"
def testMultiSANCertPEM : String := include_cert% "async_ssl_certs/multisan.pem"
def testCorruptCertPEM : String := include_cert% "async_ssl_certs/corrupt.pem"

-- Valid only in 2020.
def testExpiredCertPEM : String := include_cert% "async_ssl_certs/expired.pem"

-- `key.pem` in the traditional encoding, which `PEM_X509_INFO_read_bio` yields as a certificate-less
-- entry (PKCS#8 keys are dropped earlier).
def testTraditionalKeyPEM : String := include_cert% "async_ssl_certs/tradkey.pem"

-- The key of `intermediate.pem`; it matches none of the server certificates.
def testUnrelatedKeyPEM : String := include_cert% "async_ssl_certs/key2.pem"

-- P-256, so it mismatches the RSA certificates by algorithm.
def testECKeyPEM : String := include_cert% "async_ssl_certs/eckey.pem"

-- `key.pem` behind a passphrase.
def testEncryptedKeyPEM : String := include_cert% "async_ssl_certs/enckey.pem"

-- `key.pem` encrypted under an empty passphrase.
def testEmptyPassphraseKeyPEM : String := include_cert% "async_ssl_certs/emptypwkey.pem"

-- `cert.pem` as an encrypted `CERTIFICATE` block.
def testEncryptedCertPEM : String := include_cert% "async_ssl_certs/enccert.pem"

-- Self-signed under a 512-bit RSA key, below security level 2.
def testWeakCertPEM : String := include_cert% "async_ssl_certs/weakcert.pem"

-- Signed by `cert.pem`, so no chain can terminate at it.
def testIntermediateCertPEM : String := include_cert% "async_ssl_certs/intermediate.pem"

-- A CRL.
def testCRLPEM : String := include_cert% "async_ssl_certs/crl.pem"

-- `intermediate.pem` explicitly trusted for TLS server authentication.
def testTrustedIntermediatePEM : String := include_cert% "async_ssl_certs/trustedintermediate.pem"

-- `cert.pem` explicitly rejected for TLS server authentication.
def testRejectedCertPEM : String := include_cert% "async_ssl_certs/rejectedcert.pem"

-- A key whose algorithm cannot sign.
def testX25519KeyPEM : String := include_cert% "async_ssl_certs/x25519key.pem"

-- Three distinct certificates in one file.
def testBundlePEM : String := testCertPEM ++ testWildcardCertPEM ++ testMultiSANCertPEM

/-- Paths of the material above, for the `PEM.file` cases. -/
structure Fixtures where
  cert : String
  key : String
  unrelatedKey : String
  ecKey : String
  encKey : String
  emptyPwKey : String
  encCert : String
  expired : String
  weak : String
  intermediate : String
  /-- No PEM armour at all. -/
  junk : String
  corrupt : String
  /-- A valid leaf followed by a corrupt certificate. -/
  chain : String
  empty : String
  dir : String
  unreadable : String
  /-- A path below a regular file. -/
  nonDirParent : String

def mkFixturesIn (root : System.FilePath) : IO Fixtures := do
  let write (name contents : String) : IO String := do
    let path := toString (root / name)
    IO.FS.writeFile path contents
    return path

  let cert ← write "cert.pem" testCertPEM
  let key ← write "key.pem" testKeyPEM
  let unrelatedKey ← write "key2.pem" testUnrelatedKeyPEM
  let ecKey ← write "eckey.pem" testECKeyPEM
  let encKey ← write "enckey.pem" testEncryptedKeyPEM
  let emptyPwKey ← write "emptypwkey.pem" testEmptyPassphraseKeyPEM
  let encCert ← write "enccert.pem" testEncryptedCertPEM
  let expired ← write "expired.pem" testExpiredCertPEM
  let weak ← write "weak.pem" testWeakCertPEM
  let intermediate ← write "intermediate.pem" testIntermediateCertPEM
  let junk ← write "junk.pem" "this is not pem\n"
  let corrupt ← write "corrupt.pem" testCorruptCertPEM
  let chain ← write "chain.pem" (testCertPEM ++ testCorruptCertPEM)
  let empty ← write "empty.pem" ""

  let dir := toString (root / "subdir")
  IO.FS.createDir dir

  let unreadable ← write "secret.pem" testCertPEM
  IO.setAccessRights unreadable { user := { read := false, write := false, execution := false } }

  return { cert, key, unrelatedKey, ecKey, encKey, emptyPwKey, encCert, expired, weak,
           intermediate, junk, corrupt, chain, empty, dir, unreadable,
           nonDirParent := toString (System.FilePath.mk cert / "ca.pem") }

/-- Runs `k` against a fresh fixture directory, removed afterwards. -/
def withFixtures (k : Fixtures → IO α) : IO α :=
  IO.FS.withTempDir fun root => do k (← mkFixturesIn root)

def assertErrorMessage (label expected : String) (act : IO Unit) : IO Unit := do
  match ← act.toBaseIO with
  | .ok _ => throw <| IO.userError s!"{label}: expected failure, but it succeeded"
  | .error e =>
    let actual := toString e
    unless actual == expected do
      throw <| IO.userError s!"{label}:\nexpected error: {expected}\nactual error:   {actual}"

-- For failures whose wording depends on the platform's C library.
def assertErrorMessageOneOf (label : String) (expected : List String) (act : IO Unit) : IO Unit := do
  match ← act.toBaseIO with
  | .ok _ => throw <| IO.userError s!"{label}: expected failure, but it succeeded"
  | .error e =>
    let actual := toString e
    unless expected.contains actual do
      throw <| IO.userError s!"{label}:\nexpected one of:\n\
        {String.intercalate "\n  --- or ---\n" expected}\nactual error:   {actual}"

-- `readBinFile` stats the path through libuv, whose `ENOENT` on Windows is 4058 rather than `errno`.
def missingFileError (path : String) : String :=
  let code := if System.Platform.isWindows then 4058 else 2
  s!"no such file or directory (error code: {code})\n  file: {path}"

-- `EINVAL`: failures with no `errno` behind them, and `errno` `EINVAL` itself.
def malformedFileError (path detail : String) : String :=
  s!"invalid argument (error code: 22, {detail})\n  file: {path}"

def nulByteError (path : String) : String :=
  s!"invalid argument (error code: 22, string contains NUL bytes)\n  file: {path}"

def malformedPEMError (detail : String) : String :=
  s!"invalid argument (error code: 22, {detail})"

def caUnreadable : String := "could not read PEM CA certificates"

def caNoCerts : String := "the CA material contains no certificates"

def caNoAnchor : String :=
  "the CA material holds no certificate a chain may end at: every one is marked as distrusted"

/--
Whether the host supplies platform trust anchors. A Nix sandbox or a container without
`ca-certificates` has none; macOS and Windows always do, so a failure there fails the test.
-/
def hasSystemRoots : IO Bool := do
  match ← (discard <| Context.Client.mk).toBaseIO with
  | .ok _ => return true
  | .error e =>
    let fileBased := !System.Platform.isOSX && !System.Platform.isWindows
    match e with
    | .noSuchThing none _ _ => if fileBased then return false else throw e
    | _ => throw e

-- Smoke test.
def testContextCreation (f : Fixtures) : IO Unit := do
  let _serverCtx ← Context.Server.mk { cert := .file f.cert, key := .file f.key }

  let _clientCtx ← Context.Client.mk { trust := .insecureSkipVerify }
  let _clientCtx2 ← Context.Client.mk { trust := .system #[.file f.cert] }
  let _clientCtx3 ← Context.Client.mk { trust := .system #[.text testCertPEM] }

  if ← hasSystemRoots then
    discard <| Context.Client.mk

/-!
`Trust.only` narrows the store to the supplied CAs, so it needs at least one.
-/

def testPinnedToSuppliedCA (f : Fixtures) : IO Unit := do
  let _clientCtx ← Context.Client.mk { trust := .only #[.file f.cert] }
  let _clientCtx2 ← Context.Client.mk { trust := .only #[.text testCertPEM] }
  let _clientCtx3 ← Context.Client.mk { trust := .only #[.text testBundlePEM] }

def testPinningRejectsEmptyCA : IO Unit := do
  assertErrorMessage "pinned with no CA at all"
    (malformedPEMError "`Trust.only` needs at least one CA certificate")
    (discard <| Context.Client.mk { trust := .only #[] })

-- Empty material is a bundle without certificates, not an absent CA.
def testPinningRejectsEmptyCAMaterial : IO Unit := do
  assertErrorMessage "pinned to an empty CA string" (malformedPEMError caNoCerts)
    (discard <| Context.Client.mk { trust := .only #[.text ""] })

-- Any listed certificate can end a chain, so an intermediate CA can be trusted on its own.
def testPinningToIntermediate (f : Fixtures) : IO Unit := do
  let _clientCtx ← Context.Client.mk { trust := .only #[.text testIntermediateCertPEM] }
  let _clientCtx2 ← Context.Client.mk { trust := .only #[.file f.intermediate] }
  let _clientCtx3 ← Context.Client.mk { trust := .system #[.text testIntermediateCertPEM] }

-- Order within the bundle does not matter.
def testPinningAcceptsRootWithIntermediate : IO Unit := do
  let _clientCtx ← Context.Client.mk
    { trust := .only #[.text (testIntermediateCertPEM ++ testCertPEM)] }

  let _clientCtx2 ← Context.Client.mk
    { trust := .only #[.text (testCertPEM ++ testIntermediateCertPEM)] }

-- The bundles share one store, so the anchor may come from any of them.
def testPinningCombinesBundles (f : Fixtures) : IO Unit := do
  let _clientCtx ← Context.Client.mk
    { trust := .only #[.text testRejectedCertPEM, .file f.intermediate] }

  -- No single file is to blame for a missing anchor.
  assertErrorMessage "two bundles of distrusted roots" (malformedPEMError caNoAnchor)
    (discard <| Context.Client.mk
      { trust := .only #[.text testRejectedCertPEM, .text testRejectedCertPEM] })

  assertErrorMessage "a malformed bundle beside a good one" (malformedFileError f.junk caNoCerts)
    (discard <| Context.Client.mk { trust := .only #[.file f.cert, .file f.junk] })

/-!
`TRUSTED CERTIFICATE` trust settings override the default in either direction.
-/

def testPinningToExplicitlyTrustedIntermediate : IO Unit := do
  let _clientCtx ← Context.Client.mk { trust := .only #[.text testTrustedIntermediatePEM] }

def testPinningRejectsExplicitlyRejectedRoot : IO Unit := do
  assertErrorMessage "pinned to a root rejected for TLS servers" (malformedPEMError caNoAnchor)
    (discard <| Context.Client.mk { trust := .only #[.text testRejectedCertPEM] })

  -- The store keeps only the first copy of a repeated certificate.
  assertErrorMessage "rejected root repeated as a plain copy" (malformedPEMError caNoAnchor)
    (discard <| Context.Client.mk
      { trust := .only #[.text (testRejectedCertPEM ++ testCertPEM)] })

  let _clientCtx ← Context.Client.mk
    { trust := .only #[.text (testCertPEM ++ testRejectedCertPEM)] }

-- Unusable CA material reports the bundle failure, not "no trust anchors".
def testPinningStillValidatesCA (f : Fixtures) : IO Unit := do
  assertErrorMessage "pinned to a malformed CA file" (malformedFileError f.junk caNoCerts)
    (discard <| Context.Client.mk { trust := .only #[.file f.junk] })

  assertErrorMessage "pinned to a CA string with no certificates" (malformedPEMError caNoCerts)
    (discard <| Context.Client.mk { trust := .only #[.text "not a certificate at all"] })

/-!
`PEM.text` shares the loader with `PEM.file`; these cover only what differs: no path in the error,
and no NUL restriction.
-/

def testMkServerFromMemory (f : Fixtures) : IO Unit := do
  let _serverCtx ← Context.Server.mk { cert := .text testCertPEM, key := .text testKeyPEM }

  let _serverCtx2 ← Context.Server.mk { cert := .file f.cert, key := .text testKeyPEM }
  let _serverCtx3 ← Context.Server.mk { cert := .text testCertPEM, key := .file f.key }

  let _serverCtx4 ← Context.Server.mk
    { cert := .text (testCertPEM ++ testWildcardCertPEM), key := .text testKeyPEM }

def testMkServerFromMemoryErrors : IO Unit := do
  assertErrorMessage "malformed in-memory certificate"
    (malformedPEMError "could not read a PEM certificate chain")
    (discard <| Context.Server.mk { cert := .text "this is not pem\n", key := .text testKeyPEM })

  assertErrorMessage "mismatched in-memory key"
    (malformedPEMError "the private key does not match the certificate")
    (discard <| Context.Server.mk { cert := .text testCertPEM, key := .text testUnrelatedKeyPEM })

def testMkServerFromMemoryAcceptsNul : IO Unit := do
  let _serverCtx ← Context.Server.mk
    { cert := .text (testCertPEM.push '\x00'), key := .text testKeyPEM }

-- Repeated certificates are skipped rather than rejected.
def testMkFromPEMAcceptsBundle : IO Unit := do
  let _clientCtx ← Context.Client.mk { trust := .system #[.text testBundlePEM] }
  let _clientCtx2 ← Context.Client.mk { trust := .system #[.text (testBundlePEM ++ testCertPEM)] }

def testMkFromPEMAcceptsNulBytes : IO Unit := do
  let _clientCtx ← Context.Client.mk { trust := .system #[.text (testCertPEM.push '\x00')] }

def testMkFromPEMRejectsEmptyBlock : IO Unit := do
  assertErrorMessage "PEM without certificates" (malformedPEMError caUnreadable)
    (discard <| Context.Client.mk
      { trust := .system #[.text "-----BEGIN CERTIFICATE-----\n-----END CERTIFICATE-----\n"] })

-- Text without PEM armour is an empty bundle, not an unreadable one.
def testMkRejectsMalformedCAFile (f : Fixtures) : IO Unit := do
  assertErrorMessage "malformed CA file" (malformedFileError f.junk caNoCerts)
    (discard <| Context.Client.mk { trust := .system #[.file f.junk] })

def testMkRejectsCorruptCAFile (f : Fixtures) : IO Unit := do
  assertErrorMessage "one-bit-flipped CA file" (malformedFileError f.corrupt caUnreadable)
    (discard <| Context.Client.mk { trust := .system #[.file f.corrupt] })

def testMkRejectsMissingCAFile : IO Unit := do
  assertErrorMessage "missing CA file"
    (missingFileError "/nonexistent/path/to/ca.pem")
    (discard <| Context.Client.mk { trust := .system #[.file "/nonexistent/path/to/ca.pem"] })

def testMkServerRejectsMissingFiles (f : Fixtures) : IO Unit := do
  assertErrorMessage "missing server cert"
    (missingFileError "/nonexistent/cert.pem")
    (discard <| Context.Server.mk { cert := .file "/nonexistent/cert.pem", key := .file f.key })

  assertErrorMessage "missing server key"
    (missingFileError "/nonexistent/key.pem")
    (discard <| Context.Server.mk { cert := .file f.cert, key := .file "/nonexistent/key.pem" })

def testMkServerRejectsMalformedKey (f : Fixtures) : IO Unit := do
  assertErrorMessage "malformed server key"
    (malformedFileError f.junk "could not read an unencrypted PEM private key")
    (discard <| Context.Server.mk { cert := .file f.cert, key := .file f.junk })

def testMkServerRejectsCertAsKey (f : Fixtures) : IO Unit := do
  assertErrorMessage "certificate used as server key"
    (malformedFileError f.cert "could not read an unencrypted PEM private key")
    (discard <| Context.Server.mk { cert := .file f.cert, key := .file f.cert })

def testMkServerRejectsMalformedCert (f : Fixtures) : IO Unit := do
  assertErrorMessage "malformed server cert"
    (malformedFileError f.junk "could not read a PEM certificate chain")
    (discard <| Context.Server.mk { cert := .file f.junk, key := .file f.key })

def testMkServerRejectsCorruptCert (f : Fixtures) : IO Unit := do
  assertErrorMessage "one-bit-flipped server cert"
    (malformedFileError f.corrupt "could not read a PEM certificate chain")
    (discard <| Context.Server.mk { cert := .file f.corrupt, key := .file f.key })

def testMkServerRejectsSwappedFiles (f : Fixtures) : IO Unit := do
  assertErrorMessage "swapped server cert/key"
    (malformedFileError f.key "could not read a PEM certificate chain")
    (discard <| Context.Server.mk { cert := .file f.key, key := .file f.cert })

def testMkServerRejectsMismatchedKey (f : Fixtures) : IO Unit := do
  assertErrorMessage "server key from a different pair"
    (malformedFileError f.unrelatedKey "the private key does not match the certificate")
    (discard <| Context.Server.mk { cert := .file f.cert, key := .file f.unrelatedKey })

def testMkServerRejectsUnusableKeyAlgorithm : IO Unit := do
  assertErrorMessage "X25519 server key"
    (malformedPEMError "the private key's algorithm cannot be used for TLS")
    (discard <| Context.Server.mk { cert := .text testCertPEM, key := .text testX25519KeyPEM })

-- Only `SSL_CTX_check_private_key` catches a key of another algorithm.
def testMkServerRejectsCrossAlgorithmKey (f : Fixtures) : IO Unit := do
  assertErrorMessage "EC server key against an RSA certificate"
    (malformedFileError f.ecKey "the private key does not match the certificate")
    (discard <| Context.Server.mk { cert := .file f.cert, key := .file f.ecKey })

/-!
Encrypted PEM must be refused without prompting: OpenSSL's own callback reads `/dev/tty` and blocks.
-/

def testRejectsEncryptedMaterial (f : Fixtures) : IO Unit := do
  assertErrorMessage "passphrase-protected server key"
    (malformedFileError f.encKey "could not read an unencrypted PEM private key")
    (discard <| Context.Server.mk { cert := .file f.cert, key := .file f.encKey })

  -- An empty passphrase still counts as encrypted.
  assertErrorMessage "server key encrypted under an empty passphrase"
    (malformedFileError f.emptyPwKey "could not read an unencrypted PEM private key")
    (discard <| Context.Server.mk { cert := .file f.cert, key := .file f.emptyPwKey })

  assertErrorMessage "encrypted server certificate"
    (malformedFileError f.encCert "could not read a PEM certificate chain")
    (discard <| Context.Server.mk { cert := .file f.encCert, key := .file f.key })

  assertErrorMessage "encrypted CA certificate file"
    (malformedFileError f.encCert caUnreadable)
    (discard <| Context.Client.mk { trust := .system #[.file f.encCert] })

  assertErrorMessage "in-memory encrypted key"
    (malformedPEMError "could not read an unencrypted PEM private key")
    (discard <| Context.Server.mk { cert := .text testCertPEM, key := .text testEncryptedKeyPEM })

def testRejectsNulInPaths (f : Fixtures) : IO Unit := do
  let certPath := "cert\x00.pem"
  let keyPath := "key\x00.pem"
  let caPath := "ca\x00.pem"

  assertErrorMessage "NUL byte in server cert path" (nulByteError certPath)
    (discard <| Context.Server.mk { cert := .file certPath, key := .file f.key })

  assertErrorMessage "NUL byte in server key path" (nulByteError keyPath)
    (discard <| Context.Server.mk { cert := .file f.cert, key := .file keyPath })

  assertErrorMessage "NUL byte in CA path" (nulByteError caPath)
    (discard <| Context.Client.mk { trust := .system #[.file caPath] })

/-!
CA material must contain at least one certificate; keys and CRLs alone parse without error.
-/

def testMkRejectsCertlessCAFile (f : Fixtures) : IO Unit := do
  assertErrorMessage "CA file holding only a private key" (malformedFileError f.key caNoCerts)
    (discard <| Context.Client.mk { trust := .system #[.file f.key] })

  assertErrorMessage "zero-byte CA file" (malformedFileError f.empty caNoCerts)
    (discard <| Context.Client.mk { trust := .system #[.file f.empty] })

def testMkFromPEMRejectsCertlessPEM : IO Unit := do
  assertErrorMessage "traditional RSA key with no certificate" (malformedPEMError caNoCerts)
    (discard <| Context.Client.mk { trust := .system #[.text testTraditionalKeyPEM] })

  assertErrorMessage "CA string holding only a CRL" (malformedPEMError caNoCerts)
    (discard <| Context.Client.mk { trust := .system #[.text testCRLPEM] })

def testMkFromPEMSkipsNonCertificates : IO Unit := do
  let _clientCtx ← Context.Client.mk { trust := .system #[.text (testTraditionalKeyPEM ++ testCertPEM)] }
  let _clientCtx2 ← Context.Client.mk { trust := .system #[.text (testCertPEM ++ testTraditionalKeyPEM)] }
  let _clientCtx3 ← Context.Client.mk { trust := .system #[.text (testCRLPEM ++ testCertPEM)] }
  let _clientCtx4 ← Context.Client.mk { trust := .system #[.text (testCertPEM ++ testCRLPEM)] }

-- A file is read as bytes, like `PEM.text`: a Ctrl-Z, end of file to the Windows CRT's text mode,
-- hides nothing behind it.
def testMkReadsCAFilePastCtrlZ (f : Fixtures) : IO Unit := do
  let path := (System.FilePath.mk f.cert).withFileName "ctrlz.pem"
  IO.FS.writeFile path ("\x1a\n" ++ testCertPEM)
  let _clientCtx ← Context.Client.mk { trust := .only #[.file path] }

/-!
A NUL in `PEM.text` does not truncate the input but is junk to the PEM parser; where it sits
decides the outcome.
-/

def testMkFromPEMReadsPastNul : IO Unit := do
  let _clientCtx ← Context.Client.mk { trust := .system #[.text ("\x00\n" ++ testCertPEM)] }

-- On the marker's line it hides that certificate.
def testMkFromPEMDropsCertBehindNul : IO Unit := do
  assertErrorMessage "certificate behind an unterminated NUL" (malformedPEMError caNoCerts)
    (discard <| Context.Client.mk { trust := .system #[.text ("\x00" ++ testCertPEM)] })

-- Inside the body it corrupts the whole bundle.
def testMkFromPEMRejectsNulInsideCert : IO Unit := do
  let split := 200
  assertErrorMessage "NUL inside a certificate body" (malformedPEMError caUnreadable)
    (discard <| Context.Client.mk { trust := .system #[.text
      ((testCertPEM.take split).toString ++ "\x00" ++ (testCertPEM.drop split).toString)] })

-- The whole chain is loaded, not just the leaf.
def testMkServerRejectsCorruptChainMember (f : Fixtures) : IO Unit := do
  assertErrorMessage "corrupt intermediate in the server chain"
    (malformedFileError f.chain "could not read a PEM certificate chain")
    (discard <| Context.Server.mk { cert := .file f.chain, key := .file f.key })

-- Validity periods are checked at handshake time, not here.
def testAcceptsExpiredCert (f : Fixtures) : IO Unit := do
  let _serverCtx ← Context.Server.mk { cert := .file f.expired, key := .file f.key }
  let _clientCtx ← Context.Client.mk { trust := .system #[.text testExpiredCertPEM] }

/-!
A certificate refused by the security level is reported as such, not as unreadable PEM. The weak
certificate is paired with an unrelated key, so admitting it would fail with a different message.
-/

def weakCertError : String :=
  "the certificate is rejected by the TLS security level (key too small or signature digest too weak)"

def testMkServerRejectsWeakCert (f : Fixtures) : IO Unit := do
  assertErrorMessage "512-bit server certificate" (malformedFileError f.weak weakCertError)
    (discard <| Context.Server.mk { cert := .file f.weak, key := .file f.key })

def testMkServerRejectsWeakChainMember : IO Unit := do
  assertErrorMessage "512-bit certificate behind the leaf" (malformedPEMError weakCertError)
    (discard <| Context.Server.mk
      { cert := .text (testCertPEM ++ testWeakCertPEM), key := .text testKeyPEM })

-- The security level is not applied to CA material at load time.
def testAcceptsWeakCertAsCA (f : Fixtures) : IO Unit := do
  let _clientCtx ← Context.Client.mk { trust := .system #[.text testWeakCertPEM] }
  let _clientCtx2 ← Context.Client.mk { trust := .system #[.file f.weak] }

def testMkServerRejectsEmptyPaths (f : Fixtures) : IO Unit := do
  assertErrorMessage "empty server cert path" (missingFileError "")
    (discard <| Context.Server.mk { cert := .file "", key := .file f.key })

  assertErrorMessage "empty server key path" (missingFileError "")
    (discard <| Context.Server.mk { cert := .file f.cert, key := .file "" })

  assertErrorMessage "empty CA path" (missingFileError "")
    (discard <| Context.Client.mk { trust := .system #[.file ""] })

-- POSIX opens a directory and fails the read; Windows cannot open it at all.
def testRejectsDirectoryPaths (f : Fixtures) : IO Unit := do
  let expected :=
    [ s!"inappropriate type (error code: 21, illegal operation on a directory)\n  file: {f.dir}",
      s!"permission denied (error code: 13)\n  file: {f.dir}" ]

  assertErrorMessageOneOf "directory as server cert" expected
    (discard <| Context.Server.mk { cert := .file f.dir, key := .file f.key })

  assertErrorMessageOneOf "directory as server key" expected
    (discard <| Context.Server.mk { cert := .file f.cert, key := .file f.dir })

  assertErrorMessageOneOf "directory as CA file" expected
    (discard <| Context.Client.mk { trust := .system #[.file f.dir] })

-- A readable non-regular file is read like any other.
def testReadsNonRegularFile (f : Fixtures) : IO Unit := do
  if System.Platform.isWindows then
    return

  assertErrorMessage "character device as CA file" (malformedFileError "/dev/null" caNoCerts)
    (discard <| Context.Client.mk { trust := .system #[.file "/dev/null"] })

  assertErrorMessage "character device as server key"
    (malformedFileError "/dev/null" "could not read an unencrypted PEM private key")
    (discard <| Context.Server.mk { cert := .file f.cert, key := .file "/dev/null" })

-- Skipped when the permission bits do not bite, which is the case for a privileged user.
def testMkRejectsUnreadableCAFile (f : Fixtures) : IO Unit := do
  if (← (IO.FS.readFile f.unreadable).toBaseIO).isOk then
    return

  assertErrorMessage "CA file with no read permission"
    s!"permission denied (error code: 13)\n  file: {f.unreadable}"
    (discard <| Context.Client.mk { trust := .system #[.file f.unreadable] })

-- A path traversing a regular file is `ENOTDIR` on POSIX and `ENOENT` on Windows.
def testMkRejectsNonDirectoryParent (f : Fixtures) : IO Unit := do
  assertErrorMessageOneOf "CA path whose parent is a regular file"
    [ s!"inappropriate type (error code: 20, not a directory)\n  file: {f.nonDirParent}",
      missingFileError f.nonDirParent ]
    (discard <| Context.Client.mk { trust := .system #[.file f.nonDirParent] })

/-!
`SSL_CERT_FILE` and `SSL_CERT_DIR` replace the system's certificates for `Trust.system`. An empty
value counts as unset. Windows is skipped: libuv sets variables there through the Win32 API, which
`IO.getEnv` does not see.
-/

def withEnv (name value : String) (act : IO Unit) : IO Unit := do
  let old ← IO.getEnv name
  Std.Async.System.setEnvVar name value
  try act finally
    match old with
    | some v => Std.Async.System.setEnvVar name v
    | none => Std.Async.System.unsetEnvVar name

-- Runs `act` with exactly these values for the two variables.
def withCertEnv (file dir : String) (act : IO Unit) : IO Unit :=
  withEnv "SSL_CERT_FILE" file (withEnv "SSL_CERT_DIR" dir act)

def envNamesNoCertificate : String :=
  "no such thing (error code: 2, failed to load system trust store: SSL_CERT_FILE and SSL_CERT_DIR \
    name no certificate)"

def testCertEnvVars (f : Fixtures) : IO Unit := do
  if System.Platform.isWindows then
    return

  -- A directory of plainly named PEM files, as `c_rehash` never saw it, plus junk and a subdirectory.
  let plainDir := System.FilePath.mk f.dir / "plain"
  IO.FS.createDirAll (plainDir / "nested")
  IO.FS.writeFile (plainDir / "ca.pem") testCertPEM
  IO.FS.writeFile (plainDir / "notes.txt") "this is not pem\n"

  let junkDir := System.FilePath.mk f.dir / "junk"
  IO.FS.createDirAll junkDir
  IO.FS.writeFile (junkDir / "deadbeef.0") "this is not pem\n"

  withCertEnv f.cert "" (discard <| Context.Client.mk)
  withCertEnv "" plainDir.toString (discard <| Context.Client.mk)
  withCertEnv "" s!"/nonexistent{System.SearchPath.separator}{plainDir}" (discard <| Context.Client.mk)
  withCertEnv "/nonexistent/ca.pem" plainDir.toString (discard <| Context.Client.mk)

  for (file, dir) in [(f.junk, ""), ("/nonexistent/ca.pem", ""), ("", junkDir.toString),
      ("", "/nonexistent/certs"), (f.empty, junkDir.toString)] do
    withCertEnv file dir do
      assertErrorMessage s!"SSL_CERT_FILE={file} SSL_CERT_DIR={dir}" envNamesNoCertificate
        (discard <| Context.Client.mk)

      -- Extra CAs are still trusted.
      discard <| Context.Client.mk { trust := .system #[.text testCertPEM] }

  -- Empty values are ignored, leaving the system's certificates.
  withCertEnv "" "" do
    if ← hasSystemRoots then
      discard <| Context.Client.mk

  -- `Trust.only` never reads the environment, which would otherwise supply an anchor.
  withCertEnv f.cert "" do
    assertErrorMessage "pinned context beside an anchor in SSL_CERT_FILE"
      (malformedPEMError caNoAnchor)
      (discard <| Context.Client.mk { trust := .only #[.text testRejectedCertPEM] })

/-!
Protocol settings: the version range, and certificates on both sides of mutual TLS.
Whether they take effect is a handshake matter; these check what is accepted and refused up front.
-/

def insecure : Context.Client.Config := { trust := .insecureSkipVerify }

def testVersionRange : IO Unit := do
  let ranges : List (Version × Version) := [(.tls12, .tls12), (.tls12, .tls13), (.tls13, .tls13)]

  for (lo, hi) in ranges do
    discard <| Context.Client.mk { insecure with minVersion := lo, maxVersion := hi }
    discard <| Context.Server.mk
      { cert := .text testCertPEM, key := .text testKeyPEM, minVersion := lo, maxVersion := hi }

  let inverted := malformedPEMError "`minVersion` is above `maxVersion`"

  assertErrorMessage "client range upside down" inverted
    (discard <| Context.Client.mk { insecure with minVersion := .tls13, maxVersion := .tls12 })

  assertErrorMessage "server range upside down" inverted
    (discard <| Context.Server.mk
      { cert := .text testCertPEM, key := .text testKeyPEM, minVersion := .tls13, maxVersion := .tls12 })

def testClientAuth (f : Fixtures) : IO Unit := do
  let base : Context.Server.Config := { cert := .file f.cert, key := .file f.key }
  let modes : List Context.Server.ClientAuth :=
    [.none, .request, .requireAny, .verifyIfGiven #[.file f.cert],
     .requireAndVerify #[.text testCertPEM, .file f.intermediate]]

  for clientAuth in modes do
    discard <| Context.Server.mk { base with clientAuth }

  let noCA := malformedPEMError "verifying client certificates needs at least one CA certificate"

  assertErrorMessage "verifying against no CA" noCA
    (discard <| Context.Server.mk { base with clientAuth := .verifyIfGiven #[] })

  assertErrorMessage "requiring and verifying against no CA" noCA
    (discard <| Context.Server.mk { base with clientAuth := .requireAndVerify #[] })

  assertErrorMessage "malformed client CA file" (malformedFileError f.junk caNoCerts)
    (discard <| Context.Server.mk { base with clientAuth := .requireAndVerify #[.file f.junk] })

def testClientCredentials (f : Fixtures) : IO Unit := do
  let _clientCtx ← Context.Client.mk
    { insecure with credentials := some { cert := .file f.cert, key := .file f.key } }

  let _clientCtx2 ← Context.Client.mk
    { credentials := some { cert := .text testCertPEM, key := .text testKeyPEM } }

  assertErrorMessage "client key from a different pair"
    (malformedFileError f.unrelatedKey "the private key does not match the certificate")
    (discard <| Context.Client.mk
      { insecure with credentials := some { cert := .file f.cert, key := .file f.unrelatedKey } })

  assertErrorMessage "encrypted client key"
    (malformedFileError f.encKey "could not read an unencrypted PEM private key")
    (discard <| Context.Client.mk
      { insecure with credentials := some { cert := .file f.cert, key := .file f.encKey } })

#eval withFixtures fun f => do
  testContextCreation f
  testMkServerFromMemory f
  testMkServerFromMemoryErrors
  testMkServerFromMemoryAcceptsNul
  testMkFromPEMAcceptsBundle
  testMkFromPEMAcceptsNulBytes

-- A regression here hangs on a passphrase prompt rather than failing.
#eval withFixtures fun f => do
  testRejectsEncryptedMaterial f

-- Pinning: `Trust.only` narrows the store to the supplied CAs.
#eval withFixtures fun f => do
  testPinnedToSuppliedCA f
  testPinningRejectsEmptyCA
  testPinningRejectsEmptyCAMaterial
  testPinningStillValidatesCA f

-- Any listed certificate can end a chain, unless it is marked as distrusted.
#eval withFixtures fun f => do
  testPinningToIntermediate f
  testPinningAcceptsRootWithIntermediate
  testPinningCombinesBundles f
  testPinningToExplicitlyTrustedIntermediate
  testPinningRejectsExplicitlyRejectedRoot

-- The environment's certificates replace the system's.
#eval withFixtures fun f => do
  testCertEnvVars f

-- CA material that cannot be used as a trust anchor.
#eval withFixtures fun f => do
  testMkRejectsMissingCAFile
  testMkRejectsMalformedCAFile f
  testMkRejectsCorruptCAFile f
  testMkFromPEMRejectsEmptyBlock
  testMkRejectsCertlessCAFile f
  testMkFromPEMRejectsCertlessPEM
  testMkFromPEMSkipsNonCertificates
  testMkReadsCAFilePastCtrlZ f

-- Server credentials that do not load.
#eval withFixtures fun f => do
  testMkServerRejectsMissingFiles f
  testMkServerRejectsMalformedCert f
  testMkServerRejectsMalformedKey f
  testMkServerRejectsCorruptCert f
  testMkServerRejectsCertAsKey f
  testMkServerRejectsSwappedFiles f
  testMkServerRejectsMismatchedKey f
  testMkServerRejectsCrossAlgorithmKey f
  testMkServerRejectsUnusableKeyAlgorithm
  testMkServerRejectsCorruptChainMember f
  testRejectsNulInPaths f

-- NUL is data, not a terminator, but it is not invisible either.
#eval do
  testMkFromPEMReadsPastNul
  testMkFromPEMDropsCertBehindNul
  testMkFromPEMRejectsNulInsideCert

-- Accepted here, rejected later: the clock and the security level.
#eval withFixtures fun f => do
  testAcceptsExpiredCert f
  testMkServerRejectsWeakCert f
  testMkServerRejectsWeakChainMember
  testAcceptsWeakCertAsCA f

-- OS-level failures keep the path and the real errno.
#eval withFixtures fun f => do
  testMkRejectsUnreadableCAFile f
  testMkRejectsNonDirectoryParent f
  testMkServerRejectsEmptyPaths f
  testRejectsDirectoryPaths f
  testReadsNonRegularFile f

-- The version range and mutual TLS.
#eval withFixtures fun f => do
  testVersionRange
  testClientAuth f
  testClientCredentials f
