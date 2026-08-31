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
def testWildcardCertPEM : String := include_cert% "async_ssl_certs/wildcard.pem"
def testMultiSANCertPEM : String := include_cert% "async_ssl_certs/multisan.pem"
def testCorruptCertPEM : String := include_cert% "async_ssl_certs/corrupt.pem"

-- Validity window entirely in 2020. Building a context parses certificates without checking their
-- validity period, so this is expected to load like any other.
def testExpiredCertPEM : String := include_cert% "async_ssl_certs/expired.pem"

-- `key.pem` in the traditional (RFC 1421) encoding rather than PKCS#8. The distinction matters:
-- `PEM_X509_INFO_read_bio` drops a `BEGIN PRIVATE KEY` block entirely, but yields an entry with no
-- certificate for `BEGIN RSA PRIVATE KEY`, which is the case the loader has to skip.
def testTraditionalKeyPEM : String := include_cert% "async_ssl_certs/tradkey.pem"

-- Matches none of the certificates above, so it is only good for provoking a key/cert mismatch.
def testUnrelatedKeyPEM : String := include_cert% "async_ssl_certs/key2.pem"

-- A P-256 key, so the mismatch against the RSA certificates is one of algorithm rather than value.
def testECKeyPEM : String := include_cert% "async_ssl_certs/eckey.pem"

-- `key.pem` behind a passphrase, which OpenSSL asks for on the terminal unless it is told not to.
def testEncryptedKeyPEM : String := include_cert% "async_ssl_certs/enckey.pem"

-- `key.pem` encrypted under an *empty* passphrase, which a password callback reporting a zero-length
-- passphrase rather than a failure decrypts instead of rejecting.
def testEmptyPassphraseKeyPEM : String := include_cert% "async_ssl_certs/emptypwkey.pem"

-- `cert.pem` as an RFC 1421 encrypted `CERTIFICATE` block. Unlike an encrypted key, this is
-- decrypted in place while the bundle is read, so it reaches the password callback through a
-- different path in every constructor.
def testEncryptedCertPEM : String := include_cert% "async_ssl_certs/enccert.pem"

-- Self-signed under a 512-bit RSA key. It parses like any other certificate and is turned away by
-- the security level instead, which is a different failure from unreadable PEM.
def testWeakCertPEM : String := include_cert% "async_ssl_certs/weakcert.pem"

-- A CRL: the non-certificate bundle entry that is not a private key. It is what separates "this
-- bundle holds no certificates" from "this bundle could not be read".
def testCRLPEM : String := include_cert% "async_ssl_certs/crl.pem"

-- Three distinct certificates in one file, the shape of a real CA bundle.
def testBundlePEM : String := testCertPEM ++ testWildcardCertPEM ++ testMultiSANCertPEM

-- Writes the embedded certificate and key to a temporary directory, for the `PEM.file` cases.
def setupTestCerts : IO (String × String) := do
  let dir ← IO.FS.createTempDir
  let keyFile  := toString (dir / "key.pem")
  let certFile := toString (dir / "cert.pem")
  IO.FS.writeFile keyFile testKeyPEM
  IO.FS.writeFile certFile testCertPEM
  return (certFile, keyFile)

-- Context creation and configuration (smoke test).
def testContextCreation (certFile keyFile : String) : IO Unit := do
  let _serverCtx ← Context.Server.mk { cert := .file certFile, key := .file keyFile }

  -- Empty CA with `verifyPeer := false` disables verification without parsing any CA material.
  let _clientCtx ← Context.Client.mk { verifyPeer := false }

  -- Non-empty CA file with `verifyPeer := true` exercises the additive trust path: the system
  -- roots plus the supplied CA.
  let _clientCtx2 ← Context.Client.mk { ca := some (.file certFile) }

  -- A non-empty CA path with `verifyPeer := false` is accepted, but the CA file is not parsed.
  let _clientCtx3 ← Context.Client.mk { ca := some (.file certFile), verifyPeer := false }

  -- Defaults: no CA file, peer verification against the system trust anchors.
  let _clientCtx4 ← Context.Client.mk

-- Creating a client from an in-memory PEM string.
def testMkClientFromPEM (certFile : String) : IO Unit := do
  let caPEM ← IO.FS.readFile certFile
  let _clientCtx ← Context.Client.mk { ca := some (.text caPEM) }

-- Materializes rejected input on disk, for the `PEM.file` cases.
def writeTempFile (name contents : String) : IO String := do
  let dir ← IO.FS.createTempDir
  let path := toString (dir / name)
  IO.FS.writeFile path contents
  return path

def setupMalformedFile : IO String := writeTempFile "junk.pem" "this is not pem\n"

def setupCorruptCert : IO String := writeTempFile "corrupt.pem" testCorruptCertPEM

def setupUnrelatedKey : IO String := writeTempFile "key2.pem" testUnrelatedKeyPEM

def setupECKey : IO String := writeTempFile "eckey.pem" testECKeyPEM

def setupEncryptedKey : IO String := writeTempFile "enckey.pem" testEncryptedKeyPEM

def setupEmptyPassphraseKey : IO String := writeTempFile "emptypwkey.pem" testEmptyPassphraseKeyPEM

def setupBundle : IO String := writeTempFile "bundle.pem" testBundlePEM

def setupDuplicateBundle : IO String := writeTempFile "dup.pem" (testBundlePEM ++ testCertPEM)

def setupEncryptedCert : IO String := writeTempFile "enccert.pem" testEncryptedCertPEM

def setupExpiredCert : IO String := writeTempFile "expired.pem" testExpiredCertPEM

def setupWeakCert : IO String := writeTempFile "weak.pem" testWeakCertPEM

def setupCRL : IO String := writeTempFile "crl.pem" testCRLPEM

def setupEmptyFile : IO String := writeTempFile "empty.pem" ""

def setupDirectory : IO String := return toString (← IO.FS.createTempDir)

-- A valid leaf followed by a corrupt second certificate, i.e. a chain whose *intermediate* is bad.
def setupCorruptChain : IO String := writeTempFile "chain.pem" (testCertPEM ++ testCorruptCertPEM)

def setupUnreadableFile : IO String := do
  let path ← writeTempFile "secret.pem" testCertPEM
  IO.setAccessRights path { user := { read := false, write := false, execution := false } }
  return path

-- A path that treats a regular file as if it were a directory, which the OS refuses with ENOTDIR.
def setupNonDirectoryParent : IO String := do
  let path ← writeTempFile "notadir.pem" testCertPEM
  return toString (System.FilePath.mk path / "ca.pem")

-- Asserts that an IO action fails with exactly `expected` as its message.
def assertErrorMessage (label expected : String) (act : IO Unit) : IO Unit := do
  match ← act.toBaseIO with
  | .ok _ => throw <| IO.userError s!"{label}: expected failure, but it succeeded"
  | .error e =>
    let actual := toString e
    unless actual == expected do
      throw <| IO.userError s!"{label}:\nexpected error: {expected}\nactual error:   {actual}"

-- For a failure whose exact wording depends on the platform's C library or on OpenSSL's ambient
-- configuration. The set is spelled out so an unexpected *third* message still fails the test.
def assertErrorMessageOneOf (label : String) (expected : List String) (act : IO Unit) : IO Unit := do
  match ← act.toBaseIO with
  | .ok _ => throw <| IO.userError s!"{label}: expected failure, but it succeeded"
  | .error e =>
    let actual := toString e
    unless expected.contains actual do
      throw <| IO.userError s!"{label}:\nexpected one of:\n\
        {String.intercalate "\n  --- or ---\n" expected}\nactual error:   {actual}"

-- A missing file reaches OpenSSL's error queue as an `ENOENT` entry, which is turned back into the
-- corresponding `IO.Error` on the offending path.
def missingFileError (path : String) : String :=
  s!"no such file or directory (error code: 2)\n  file: {path}"

-- Failures with no `errno` behind them (unparsable PEM, key/cert mismatch) are reported as `EINVAL`
-- plus a description of what went wrong with the material on the offending path.
def malformedFileError (path detail : String) : String :=
  s!"invalid argument (error code: 22, {detail})\n  file: {path}"

-- A path is rejected before it reaches OpenSSL if it cannot be passed as a C string.
def nulByteError (path : String) : String :=
  s!"invalid argument (error code: 22, string contains NUL bytes)\n  file: {path}"

-- The in-memory variants report the same way, but have no path to attach.
def malformedPEMError (detail : String) : String :=
  s!"invalid argument (error code: 22, {detail})"

-- An empty CA bundle with `verifyPeer := true` falls back to the platform trust anchors and succeeds.
def testMkFromPEMEmptyFallsBack : IO Unit := do
  let _clientCtx ← Context.Client.mk {}

/-!
`trustSystemRoots := false` narrows the store to the supplied CA, which is what pinning against a
private authority needs. The store a context starts with is empty, so excluding the platform anchors
without naming a CA would leave nothing to verify against — a context that could never complete a
handshake. That is refused at construction instead of at connection time.
-/

def noAnchorsError : String :=
  malformedPEMError "no trust anchors: peer verification is on, the platform trust anchors are \
    excluded, and no CA certificate was given"

def testPinnedToSuppliedCA (certFile : String) : IO Unit := do
  let _clientCtx ← Context.Client.mk { ca := some (.file certFile), trustSystemRoots := false }
  let _clientCtx2 ← Context.Client.mk { ca := some (.text testCertPEM), trustSystemRoots := false }
  let _clientCtx3 ← Context.Client.mk { ca := some (.text testBundlePEM), trustSystemRoots := false }

def testPinningRejectsEmptyCA : IO Unit := do
  assertErrorMessage "pinned with no CA at all" noAnchorsError
    (discard <| Context.Client.mk { trustSystemRoots := false })

-- `ca := some` is a claim that anchors were supplied, so empty material is a bundle that holds no
-- certificate rather than an absent one. That is a different diagnosis from the case above, and the
-- more specific of the two.
def testPinningRejectsEmptyCAMaterial : IO Unit := do
  assertErrorMessage "pinned to an empty CA string"
    (malformedPEMError "the given CA PEM string contains no certificates")
    (discard <| Context.Client.mk { ca := some (.text ""), trustSystemRoots := false })

-- With verification off there is no store to be empty, so excluding the platform anchors is not a
-- contradiction and `trustSystemRoots` is simply ignored.
def testPinningIgnoredWithoutVerification : IO Unit := do
  let _clientCtx ← Context.Client.mk { verifyPeer := false, trustSystemRoots := false }

-- Supplied CA material still has to yield a certificate. These reach the ordinary bundle-loading
-- failures rather than the "no trust anchors" one, which is what pins the check to the *absence* of
-- CA material rather than to it being unusable.
def testPinningStillValidatesCA (junkFile : String) : IO Unit := do
  assertErrorMessage "pinned to a malformed CA file"
    (malformedFileError junkFile "the CA file contains no certificates")
    (discard <| Context.Client.mk { ca := some (.file junkFile), trustSystemRoots := false })

  assertErrorMessage "pinned to a CA string with no certificates"
    (malformedPEMError "the given CA PEM string contains no certificates")
    (discard <| Context.Client.mk
      { ca := some (.text "not a certificate at all"), trustSystemRoots := false })

-- An unusable path is still rejected as a path, before the anchor bookkeeping is consulted.
def testPinningRejectsNulInCAFile : IO Unit := do
  let caPath := "ca\x00.pem"

  assertErrorMessage "NUL byte in a pinned CA path" (nulByteError caPath)
    (discard <| Context.Client.mk { ca := some (.file caPath), trustSystemRoots := false })

/-!
Server credentials may be supplied in memory rather than by path, for a certificate that comes from
a secret manager or is embedded in the binary. `PEM.text` reads with an explicit length, so unlike a
path it carries no NUL restriction; the failures it reports have no path to name.
-/

def testMkServerFromMemory : IO Unit := do
  let _serverCtx ← Context.Server.mk { cert := .text testCertPEM, key := .text testKeyPEM }

-- The two sources are independent, so a file certificate pairs with an in-memory key and back.
def testMkServerMixedSources (certFile keyFile : String) : IO Unit := do
  let _serverCtx ← Context.Server.mk { cert := .file certFile, key := .text testKeyPEM }
  let _serverCtx2 ← Context.Server.mk { cert := .text testCertPEM, key := .file keyFile }

-- The whole chain is loaded from memory too, not just the leaf.
def testMkServerFromMemoryLoadsChain : IO Unit := do
  let _serverCtx ← Context.Server.mk
    { cert := .text (testCertPEM ++ testWildcardCertPEM), key := .text testKeyPEM }

  assertErrorMessage "corrupt intermediate in an in-memory chain"
    (malformedPEMError "could not read a PEM certificate chain")
    (discard <| Context.Server.mk
      { cert := .text (testCertPEM ++ testCorruptCertPEM), key := .text testKeyPEM })

-- In-memory failures report the same diagnoses as the path-based ones, without a path attached.
def testMkServerFromMemoryErrors : IO Unit := do
  assertErrorMessage "malformed in-memory certificate"
    (malformedPEMError "could not read a PEM certificate chain")
    (discard <| Context.Server.mk { cert := .text "this is not pem\n", key := .text testKeyPEM })

  assertErrorMessage "malformed in-memory key"
    (malformedPEMError "could not read an unencrypted PEM private key")
    (discard <| Context.Server.mk { cert := .text testCertPEM, key := .text "this is not pem\n" })

  assertErrorMessage "mismatched in-memory key"
    (malformedPEMError "the private key does not match the certificate")
    (discard <| Context.Server.mk { cert := .text testCertPEM, key := .text testUnrelatedKeyPEM })

  assertErrorMessage "cross-algorithm in-memory key"
    (malformedPEMError "the private key does not match the certificate")
    (discard <| Context.Server.mk { cert := .text testCertPEM, key := .text testECKeyPEM })

-- Encrypted material must be refused without prompting here too, which is the failure mode that
-- hangs rather than fails loudly.
def testMkServerFromMemoryRejectsEncrypted : IO Unit := do
  assertErrorMessage "in-memory encrypted key"
    (malformedPEMError "could not read an unencrypted PEM private key")
    (discard <| Context.Server.mk { cert := .text testCertPEM, key := .text testEncryptedKeyPEM })

  assertErrorMessage "in-memory empty-passphrase key"
    (malformedPEMError "could not read an unencrypted PEM private key")
    (discard <| Context.Server.mk
      { cert := .text testCertPEM, key := .text testEmptyPassphraseKeyPEM })

  assertErrorMessage "in-memory encrypted certificate"
    (malformedPEMError "could not read a PEM certificate chain")
    (discard <| Context.Server.mk { cert := .text testEncryptedCertPEM, key := .text testKeyPEM })

-- A path cannot carry a NUL, but in-memory material is read with a length, so it can.
def testMkServerFromMemoryAcceptsNul : IO Unit := do
  let _serverCtx ← Context.Server.mk
    { cert := .text (testCertPEM.push '\x00'), key := .text testKeyPEM }

-- `verifyPeer := false` succeeds without parsing the CA material, even for a real bundle.
def testMkFromPEMNoVerify (certFile : String) : IO Unit := do
  let caPEM ← IO.FS.readFile certFile
  let _clientCtx ← Context.Client.mk { ca := some (.text caPEM), verifyPeer := false }

-- A bundle of several distinct certificates is loaded in full: every certificate in the PEM becomes
-- a trust anchor, not just the first one.
def testMkFromPEMAcceptsBundle : IO Unit := do
  let _clientCtx ← Context.Client.mk { ca := some (.text testBundlePEM) }

def testMkAcceptsBundleFile (bundleFile : String) : IO Unit := do
  let _clientCtx ← Context.Client.mk { ca := some (.file bundleFile) }

-- Repeated certificates are skipped instead of failing, so a bundle that overlaps the system trust
-- anchors (or repeats itself) still yields a usable context.
def testMkFromPEMAcceptsDuplicates : IO Unit := do
  let _clientCtx ← Context.Client.mk { ca := some (.text (testCertPEM ++ testCertPEM)) }

def testMkAcceptsDuplicatesInFile (dupFile : String) : IO Unit := do
  let _clientCtx ← Context.Client.mk { ca := some (.file dupFile) }

-- Unlike `PEM.file`, `PEM.text` hands OpenSSL an explicit length rather than a C string,
-- so a NUL byte is data (here: trailing junk after a complete certificate) and not an error.
def testMkFromPEMAcceptsNulBytes : IO Unit := do
  let _clientCtx ← Context.Client.mk { ca := some (.text (testCertPEM.push '\x00')) }

def testMkFromPEMRejectsGarbage : IO Unit := do
  assertErrorMessage "garbage PEM"
    (malformedPEMError "the given CA PEM string contains no certificates")
    (discard <| Context.Client.mk { ca := some (.text "not a certificate at all") })

def testMkNoVerifyIgnoresCorruptCAFile (corruptFile : String) : IO Unit := do
  let _clientCtx ← Context.Client.mk { ca := some (.file corruptFile), verifyPeer := false }

def testMkFromPEMRejectsEmptyBlock : IO Unit := do
  assertErrorMessage "PEM without certificates"
    (malformedPEMError "could not read PEM CA certificates from the given string")
    (discard <| Context.Client.mk
      { ca := some (.text "-----BEGIN CERTIFICATE-----\n-----END CERTIFICATE-----\n") })

def testMkFromPEMRejectsCorruptCert : IO Unit := do
  assertErrorMessage "one-bit-flipped CA PEM"
    (malformedPEMError "could not read PEM CA certificates from the given string")
    (discard <| Context.Client.mk { ca := some (.text testCorruptCertPEM) })

-- Text with no PEM armour at all parses to an empty bundle rather than failing to parse, so it is
-- reported as "no certificates" — the same way `PEM.text` reports the same bytes.
def testMkRejectsMalformedCAFile (junkFile : String) : IO Unit := do
  assertErrorMessage "malformed CA file"
    (malformedFileError junkFile "the CA file contains no certificates")
    (discard <| Context.Client.mk { ca := some (.file junkFile) })

def testMkRejectsCorruptCAFile (corruptFile : String) : IO Unit := do
  assertErrorMessage "one-bit-flipped CA file"
    (malformedFileError corruptFile "could not read PEM CA certificates")
    (discard <| Context.Client.mk { ca := some (.file corruptFile) })

def testMkRejectsMissingCAFile : IO Unit := do
  assertErrorMessage "missing CA file"
    (missingFileError "/nonexistent/path/to/ca.pem")
    (discard <| Context.Client.mk { ca := some (.file "/nonexistent/path/to/ca.pem") })

def testMkServerRejectsMissingCert (keyFile : String) : IO Unit := do
  assertErrorMessage "missing server cert"
    (missingFileError "/nonexistent/cert.pem")
    (discard <| Context.Server.mk { cert := .file "/nonexistent/cert.pem", key := .file keyFile })

def testMkServerRejectsMissingKey (certFile : String) : IO Unit := do
  assertErrorMessage "missing server key"
    (missingFileError "/nonexistent/key.pem")
    (discard <| Context.Server.mk { cert := .file certFile, key := .file "/nonexistent/key.pem" })

def testMkServerRejectsMalformedKey (certFile junkFile : String) : IO Unit := do
  assertErrorMessage "malformed server key"
    (malformedFileError junkFile "could not read an unencrypted PEM private key")
    (discard <| Context.Server.mk { cert := .file certFile, key := .file junkFile })

def testMkServerRejectsCertAsKey (certFile : String) : IO Unit := do
  assertErrorMessage "certificate used as server key"
    (malformedFileError certFile "could not read an unencrypted PEM private key")
    (discard <| Context.Server.mk { cert := .file certFile, key := .file certFile })

def testMkServerRejectsMalformedCert (junkFile keyFile : String) : IO Unit := do
  assertErrorMessage "malformed server cert"
    (malformedFileError junkFile "could not read a PEM certificate chain")
    (discard <| Context.Server.mk { cert := .file junkFile, key := .file keyFile })

def testMkServerRejectsCorruptCert (corruptFile keyFile : String) : IO Unit := do
  assertErrorMessage "one-bit-flipped server cert"
    (malformedFileError corruptFile "could not read a PEM certificate chain")
    (discard <| Context.Server.mk { cert := .file corruptFile, key := .file keyFile })

def testMkServerRejectsSwappedFiles (certFile keyFile : String) : IO Unit := do
  assertErrorMessage "swapped server cert/key"
    (malformedFileError keyFile "could not read a PEM certificate chain")
    (discard <| Context.Server.mk { cert := .file keyFile, key := .file certFile })

def testMkServerRejectsMismatchedKey (certFile key2File : String) : IO Unit := do
  assertErrorMessage "server key from a different pair"
    (malformedFileError key2File "the private key does not match the certificate")
    (discard <| Context.Server.mk { cert := .file certFile, key := .file key2File })

-- A key of a different algorithm than the certificate lands in an unused slot of the context, so
-- `SSL_CTX_use_PrivateKey_file` accepts it without ever comparing the two; only the separate
-- `SSL_CTX_check_private_key` rejects it.
def testMkServerRejectsCrossAlgorithmKey (certFile ecKeyFile : String) : IO Unit := do
  assertErrorMessage "EC server key against an RSA certificate"
    (malformedFileError ecKeyFile "the private key does not match the certificate")
    (discard <| Context.Server.mk { cert := .file certFile, key := .file ecKeyFile })

-- Encrypted keys are unsupported. The point of this test is as much the absence of output as the
-- error itself: with no password callback installed OpenSSL prompts for the passphrase on the
-- terminal, which blocks when one is attached and pollutes the test output when one is not.
def testMkServerRejectsEncryptedKey (certFile encKeyFile : String) : IO Unit := do
  assertErrorMessage "passphrase-protected server key"
    (malformedFileError encKeyFile "could not read an unencrypted PEM private key")
    (discard <| Context.Server.mk { cert := .file certFile, key := .file encKeyFile })

-- An empty passphrase still counts as encrypted. A password callback that reports a zero-length
-- passphrase instead of a failure decrypts this key and accepts it.
def testMkServerRejectsEmptyPassphraseKey (certFile emptyPwKeyFile : String) : IO Unit := do
  assertErrorMessage "server key encrypted under an empty passphrase"
    (malformedFileError emptyPwKeyFile "could not read an unencrypted PEM private key")
    (discard <| Context.Server.mk { cert := .file certFile, key := .file emptyPwKeyFile })

def testMkServerRejectsNulInCert (keyFile : String) : IO Unit := do
  let certPath := "cert\x00.pem"

  assertErrorMessage "NUL byte in server cert path"
    (nulByteError certPath)
    (discard <| Context.Server.mk { cert := .file certPath, key := .file keyFile })

def testMkServerRejectsNulInKey (certFile : String) : IO Unit := do
  let keyPath := "key\x00.pem"

  assertErrorMessage "NUL byte in server key path"
    (nulByteError keyPath)
    (discard <| Context.Server.mk { cert := .file certFile, key := .file keyPath })

-- The CA path is checked before `verifyPeer`, so a NUL is rejected even when the file would never
-- have been opened.
def testMkRejectsNulInCAFile : IO Unit := do
  let caPath := "ca\x00.pem"

  assertErrorMessage "NUL byte in CA path"
    (nulByteError caPath)
    (discard <| Context.Client.mk { ca := some (.file caPath) })

  assertErrorMessage "NUL byte in CA path without verification"
    (nulByteError caPath)
    (discard <| Context.Client.mk { ca := some (.file caPath), verifyPeer := false })

/-!
Encrypted PEM material must be rejected outright. A passphrase callback reporting failure is what
prevents OpenSSL falling back to its own callback, which prompts on `/dev/tty` and blocks forever —
a hang that no amount of redirecting stdin escapes. `enckey.pem` and `emptypwkey.pem` cover the
private key; the tests here cover an encrypted *certificate*, which is read by a different code path
in each of the three constructors.
-/

def testMkServerRejectsEncryptedCert (encCertFile keyFile : String) : IO Unit := do
  assertErrorMessage "encrypted server certificate"
    (malformedFileError encCertFile "could not read a PEM certificate chain")
    (discard <| Context.Server.mk { cert := .file encCertFile, key := .file keyFile })

def testMkRejectsEncryptedCertCAFile (encCertFile : String) : IO Unit := do
  assertErrorMessage "encrypted CA certificate file"
    (malformedFileError encCertFile "could not read PEM CA certificates")
    (discard <| Context.Client.mk { ca := some (.file encCertFile) })

def testMkFromPEMRejectsEncryptedCert : IO Unit := do
  assertErrorMessage "encrypted CA certificate string"
    (malformedPEMError "could not read PEM CA certificates from the given string")
    (discard <| Context.Client.mk { ca := some (.text testEncryptedCertPEM) })

-- A CA bundle is required to contain at least one certificate. A file holding only a key parses
-- without complaint and would leave the trust store silently unchanged, so the count is checked
-- explicitly.
def testMkRejectsCertlessCAFile (keyFile : String) : IO Unit := do
  assertErrorMessage "CA file holding only a private key"
    (malformedFileError keyFile "the CA file contains no certificates")
    (discard <| Context.Client.mk { ca := some (.file keyFile) })

def testMkFromPEMRejectsCertlessPEM : IO Unit := do
  assertErrorMessage "CA string holding only a private key"
    (malformedPEMError "the given CA PEM string contains no certificates")
    (discard <| Context.Client.mk { ca := some (.text testKeyPEM) })

-- Non-certificate entries in a bundle are skipped rather than rejected. A *traditional* RSA key is
-- the case that matters: it yields a parsed entry carrying no certificate, unlike the PKCS#8 form
-- which is dropped before that point.
def testMkFromPEMSkipsTraditionalKey : IO Unit := do
  let _clientCtx ← Context.Client.mk { ca := some (.text (testTraditionalKeyPEM ++ testCertPEM)) }
  let _clientCtx2 ← Context.Client.mk { ca := some (.text (testCertPEM ++ testTraditionalKeyPEM)) }

def testMkFromPEMRejectsTraditionalKeyOnly : IO Unit := do
  assertErrorMessage "traditional RSA key with no certificate"
    (malformedPEMError "the given CA PEM string contains no certificates")
    (discard <| Context.Client.mk { ca := some (.text testTraditionalKeyPEM) })

/-!
`PEM.text` hands OpenSSL an explicit length rather than a C string, so a NUL does not truncate the
input. It is still junk to the PEM parser, which needs `-----BEGIN` to start a line, so where the
NUL sits decides between three outcomes. Appending a NUL to a complete certificate would pass either
way, so these put material the parser must still reach *after* the NUL.
-/

-- Terminated by a newline the NUL is skipped like any other junk line.
def testMkFromPEMReadsPastNul : IO Unit := do
  let _clientCtx ← Context.Client.mk { ca := some (.text ("\x00\n" ++ testCertPEM)) }

def testMkFromPEMParsesPastNul : IO Unit := do
  assertErrorMessage "corrupt certificate after a NUL byte"
    (malformedPEMError "could not read PEM CA certificates from the given string")
    (discard <| Context.Client.mk { ca := some (.text (testCertPEM ++ "\x00\n" ++ testCorruptCertPEM)) })

-- Sharing a line with the marker, the NUL hides it and that certificate is dropped without an error
-- of its own; only the empty bundle behind it is reported.
def testMkFromPEMDropsCertBehindNul : IO Unit := do
  assertErrorMessage "certificate behind an unterminated NUL"
    (malformedPEMError "the given CA PEM string contains no certificates")
    (discard <| Context.Client.mk { ca := some (.text ("\x00" ++ testCertPEM)) })

-- Inside the body the NUL corrupts the block, which discards the whole bundle rather than just that
-- certificate.
def testMkFromPEMRejectsNulInsideCert : IO Unit := do
  let split := 200
  assertErrorMessage "NUL inside a certificate body"
    (malformedPEMError "could not read PEM CA certificates from the given string")
    (discard <| Context.Client.mk { ca := some (.text
      ((testCertPEM.take split).toString ++ "\x00" ++ (testCertPEM.drop split).toString)) })

-- Inside the marker's type name the line still opens a block, but the name no longer matches the one
-- on the `-----END` line, so the whole string is rejected instead of that certificate being skipped.
-- This is the boundary against `testMkFromPEMDropsCertBehindNul`, where the NUL lands in the fixed
-- `-----BEGIN ` prefix instead and stops the line opening a block at all.
def testMkFromPEMRejectsNulInMarkerName : IO Unit := do
  assertErrorMessage "NUL inside a PEM marker's type name"
    (malformedPEMError "could not read PEM CA certificates from the given string")
    (discard <| Context.Client.mk { ca := some (.text
      (testCertPEM.replace "-----BEGIN CERTIFICATE-----" "-----BEGIN CERTI\x00FICATE-----")) })

-- The block is already open by the time the `-----END` line is read, so a NUL anywhere in it leaves a
-- block that can never be closed and the whole string is rejected.
def testMkFromPEMRejectsNulInEndMarker : IO Unit := do
  assertErrorMessage "NUL inside the END marker"
    (malformedPEMError "could not read PEM CA certificates from the given string")
    (discard <| Context.Client.mk { ca := some (.text
      (testCertPEM.replace "-----END CERTIFICATE-----" "-----END CERTI\x00FICATE-----")) })

-- The whole chain is loaded, not just the leaf, so a corrupt certificate in a later position is
-- still rejected. This is the observable difference between `SSL_CTX_use_certificate_chain_file`
-- and `SSL_CTX_use_certificate_file`.
def testMkServerRejectsCorruptChainMember (chainFile keyFile : String) : IO Unit := do
  assertErrorMessage "corrupt intermediate in the server chain"
    (malformedFileError chainFile "could not read a PEM certificate chain")
    (discard <| Context.Server.mk { cert := .file chainFile, key := .file keyFile })

-- Building a context parses certificates; it does not check their validity period. An expired
-- certificate is therefore accepted here and only rejected at handshake time.
def testAcceptsExpiredCert (expiredFile keyFile : String) : IO Unit := do
  let _serverCtx ← Context.Server.mk { cert := .file expiredFile, key := .file keyFile }
  let _clientCtx ← Context.Client.mk { ca := some (.text testExpiredCertPEM) }

/-!
A certificate can be refused on policy grounds rather than because it could not be read: the TLS
security level turns away an RSA key that is too short. Reporting that as unparsable PEM sends the
reader after a problem their file does not have. The key is 512 bits so that every level a build may
default to rejects it — OpenSSL defaults to level 2 only since 3.2, and level 1 still admits 1024.

The level is not ours to fix, though: a context inherits it from the ambient `openssl.cnf`, and a build
configured `DEFAULT@SECLEVEL=0` admits the certificate outright. `weakCertFile` is therefore paired with
an unrelated key, so the load fails either way and the two failures can be told apart.
-/

def testMkServerRejectsWeakCert (weakCertFile keyFile : String) : IO Unit := do
  assertErrorMessageOneOf "512-bit server certificate"
    [ malformedFileError weakCertFile
        "the certificate is rejected by the TLS security level (key too small or signature digest too weak)",
      malformedFileError keyFile "the private key does not match the certificate" ]
    (discard <| Context.Server.mk { cert := .file weakCertFile, key := .file keyFile })

-- The security level governs the certificate a server presents, not the anchors a client trusts, so
-- the very file rejected above still loads as a CA. This is what pins the diagnosis to the security
-- level rather than to the certificate being malformed.
def testAcceptsWeakCertAsCA (weakCertFile : String) : IO Unit := do
  let _clientCtx ← Context.Client.mk { ca := some (.text testWeakCertPEM) }
  let _clientCtx2 ← Context.Client.mk { ca := some (.file weakCertFile) }

/-!
A bundle entry that is not a certificate is skipped, and a bundle of nothing but such entries is
rejected for holding no certificates. `tradkey.pem` covers the private-key form; a CRL is the other
one, and the only one the "a lone CRL" case in the loader is actually about.
-/

def testMkRejectsCRLOnlyCAFile (crlFile : String) : IO Unit := do
  assertErrorMessage "CA file holding only a CRL"
    (malformedFileError crlFile "the CA file contains no certificates")
    (discard <| Context.Client.mk { ca := some (.file crlFile) })

def testMkFromPEMRejectsCRLOnly : IO Unit := do
  assertErrorMessage "CA string holding only a CRL"
    (malformedPEMError "the given CA PEM string contains no certificates")
    (discard <| Context.Client.mk { ca := some (.text testCRLPEM) })

def testMkFromPEMSkipsCRL : IO Unit := do
  let _clientCtx ← Context.Client.mk { ca := some (.text (testCRLPEM ++ testCertPEM)) }
  let _clientCtx2 ← Context.Client.mk { ca := some (.text (testCertPEM ++ testCRLPEM)) }

-- A zero-byte file has no PEM armour to fail on, so it parses to an empty bundle and is reported as
-- holding no certificates rather than as unreadable.
def testMkRejectsEmptyCAFile (emptyFile : String) : IO Unit := do
  assertErrorMessage "zero-byte CA file"
    (malformedFileError emptyFile "the CA file contains no certificates")
    (discard <| Context.Client.mk { ca := some (.file emptyFile) })

-- Only the *CA* path treats "" as "use the platform anchors". The server has no such fallback, so an
-- empty path reaches the OS and fails there.
def testMkServerRejectsEmptyPaths (certFile keyFile : String) : IO Unit := do
  assertErrorMessage "empty server cert path"
    (missingFileError "")
    (discard <| Context.Server.mk { cert := .file "", key := .file keyFile })

  assertErrorMessage "empty server key path"
    (missingFileError "")
    (discard <| Context.Server.mk { cert := .file certFile, key := .file "" })

/-!
The path is reported with the failure whenever the `IO.Error` constructor has room for it. These
also pin the errno itself, which is what would catch a platform decoding an OS error code through
the wrong table.
-/

-- Anything that is not a regular file is classified from its mode rather than by opening it, because
-- opening is not a reliable test: POSIX `fopen` succeeds on a directory and fails only at the first
-- read, and a FIFO blocks until a writer appears. The note is *appended* to the failure OpenSSL
-- actually reported rather than replacing it, because the file type need not be what went wrong —
-- OpenSSL reads a FIFO or a `/dev/fd` entry as happily as a file on disk, so a mismatched key reached
-- through one still has to say so.
def testRejectsDirectoryPaths (dir certFile keyFile : String) : IO Unit := do
  let note := " (the path is not a regular file)"

  assertErrorMessage "directory as server cert"
    (malformedFileError dir ("could not read a PEM certificate chain" ++ note))
    (discard <| Context.Server.mk { cert := .file dir, key := .file keyFile })

  assertErrorMessage "directory as server key"
    (malformedFileError dir ("could not read an unencrypted PEM private key" ++ note))
    (discard <| Context.Server.mk { cert := .file certFile, key := .file dir })

  -- Which failure this is depends on the C library. On POSIX `BIO_new_file` opens the directory and
  -- the read that follows yields nothing, so the empty bundle is what gets reported; the Windows CRT
  -- cannot open a directory as a stream at all, so the BIO is null and the path is unreadable instead.
  -- Either way the note has to be appended rather than substituted, or which of the two it was is lost.
  assertErrorMessageOneOf "directory as CA file"
    [ malformedFileError dir ("the CA file contains no certificates" ++ note),
      malformedFileError dir ("could not read PEM CA certificates" ++ note) ]
    (discard <| Context.Client.mk { ca := some (.file dir) })

-- A character device is the readable non-regular file: OpenSSL opens `/dev/null` and reads it to
-- completion, so the diagnosis is about what the empty read produced and the file type is only a
-- footnote.
def testAppendsNoteToReadableNonRegularFile (certFile : String) : IO Unit := do
  if System.Platform.isWindows then
    return

  assertErrorMessage "character device as CA file"
    (malformedFileError "/dev/null"
      "the CA file contains no certificates (the path is not a regular file)")
    (discard <| Context.Client.mk { ca := some (.file "/dev/null") })

  assertErrorMessage "character device as server key"
    (malformedFileError "/dev/null"
      "could not read an unencrypted PEM private key (the path is not a regular file)")
    (discard <| Context.Server.mk { cert := .file certFile, key := .file "/dev/null" })

-- Skipped when the permission bits do not bite, which is the case for a privileged user.
def testMkRejectsUnreadableCAFile (unreadableFile : String) : IO Unit := do
  if (← (IO.FS.readFile unreadableFile).toBaseIO).isOk then
    return

  assertErrorMessage "CA file with no read permission"
    s!"permission denied (error code: 13)\n  file: {unreadableFile}"
    (discard <| Context.Client.mk { ca := some (.file unreadableFile) })

def testMkRejectsNonDirectoryParent (notADirPath : String) : IO Unit := do
  assertErrorMessage "CA path whose parent is a regular file"
    s!"inappropriate type (error code: 20, not a directory)\n  file: {notADirPath}"
    (discard <| Context.Client.mk { ca := some (.file notADirPath) })

#eval do
  let (certFile, keyFile) ← setupTestCerts
  testContextCreation certFile keyFile

#eval do
  let (certFile, _) ← setupTestCerts
  testMkClientFromPEM certFile

-- Server credentials supplied in memory rather than by path.
#eval do
  let (certFile, keyFile) ← setupTestCerts

  testMkServerFromMemory
  testMkServerMixedSources certFile keyFile
  testMkServerFromMemoryLoadsChain
  testMkServerFromMemoryErrors
  testMkServerFromMemoryRejectsEncrypted
  testMkServerFromMemoryAcceptsNul

#eval testMkFromPEMEmptyFallsBack

-- Pinning: the supplied CA replaces the platform anchors rather than joining them.
#eval do
  let (certFile, _) ← setupTestCerts

  testPinnedToSuppliedCA certFile
  testPinningRejectsEmptyCA
  testPinningRejectsEmptyCAMaterial
  testPinningIgnoredWithoutVerification
  testPinningStillValidatesCA (← setupMalformedFile)
  testPinningRejectsNulInCAFile

#eval do
  let (certFile, _) ← setupTestCerts
  testMkFromPEMNoVerify certFile

#eval do
  testMkFromPEMAcceptsBundle
  testMkFromPEMAcceptsDuplicates
  testMkFromPEMAcceptsNulBytes
  testMkAcceptsBundleFile (← setupBundle)
  testMkAcceptsDuplicatesInFile (← setupDuplicateBundle)

#eval
  testMkFromPEMRejectsGarbage

#eval
  testMkFromPEMRejectsEmptyBlock

#eval
  testMkRejectsMissingCAFile

#eval do
  let junkFile ← setupMalformedFile
  testMkRejectsMalformedCAFile junkFile

#eval testMkFromPEMRejectsCorruptCert

#eval do
  let corruptFile ← setupCorruptCert
  testMkRejectsCorruptCAFile corruptFile
  testMkNoVerifyIgnoresCorruptCAFile corruptFile

#eval do
  let (certFile, keyFile) ← setupTestCerts
  let junkFile ← setupMalformedFile
  let corruptFile ← setupCorruptCert

  testMkServerRejectsMissingCert keyFile
  testMkServerRejectsMissingKey certFile
  testMkServerRejectsMalformedCert junkFile keyFile
  testMkServerRejectsMalformedKey certFile junkFile
  testMkServerRejectsCorruptCert corruptFile keyFile
  testMkServerRejectsCertAsKey certFile
  testMkServerRejectsSwappedFiles certFile keyFile
  testMkServerRejectsMismatchedKey certFile (← setupUnrelatedKey)
  testMkServerRejectsCrossAlgorithmKey certFile (← setupECKey)
  testMkServerRejectsEncryptedKey certFile (← setupEncryptedKey)
  testMkServerRejectsEmptyPassphraseKey certFile (← setupEmptyPassphraseKey)

#eval do
  let (certFile, keyFile) ← setupTestCerts
  testMkServerRejectsNulInCert keyFile
  testMkServerRejectsNulInKey certFile
  testMkRejectsNulInCAFile

-- Encrypted PEM in all three constructors. A regression here does not fail loudly: it blocks on a
-- passphrase prompt, so keep these ahead of anything that would mask a hang.
#eval do
  let (_, keyFile) ← setupTestCerts
  let encCertFile ← setupEncryptedCert

  testMkServerRejectsEncryptedCert encCertFile keyFile
  testMkRejectsEncryptedCertCAFile encCertFile
  testMkFromPEMRejectsEncryptedCert

-- A CA bundle must actually contain a certificate.
#eval do
  let (_, keyFile) ← setupTestCerts

  testMkRejectsCertlessCAFile keyFile
  testMkFromPEMRejectsCertlessPEM
  testMkFromPEMSkipsTraditionalKey
  testMkFromPEMRejectsTraditionalKeyOnly

-- NUL is data, not a terminator, but it is not invisible either.
#eval do
  testMkFromPEMReadsPastNul
  testMkFromPEMParsesPastNul
  testMkFromPEMDropsCertBehindNul
  testMkFromPEMRejectsNulInsideCert
  testMkFromPEMRejectsNulInMarkerName
  testMkFromPEMRejectsNulInEndMarker

#eval do
  let (certFile, keyFile) ← setupTestCerts

  testMkServerRejectsCorruptChainMember (← setupCorruptChain) keyFile
  testAcceptsExpiredCert (← setupExpiredCert) keyFile
  testMkClientFromPEM certFile

-- Rejected on policy, not for being unreadable.
#eval do
  let (_, keyFile) ← setupTestCerts
  let weakCertFile ← setupWeakCert

  testMkServerRejectsWeakCert weakCertFile keyFile
  testAcceptsWeakCertAsCA weakCertFile

-- A bundle must hold a certificate, and a CRL is not one.
#eval do
  let crlFile ← setupCRL

  testMkRejectsCRLOnlyCAFile crlFile
  testMkFromPEMRejectsCRLOnly
  testMkFromPEMSkipsCRL
  testMkRejectsEmptyCAFile (← setupEmptyFile)

-- OS-level failures keep the path and the real errno.
#eval do
  let (certFile, keyFile) ← setupTestCerts

  testMkRejectsUnreadableCAFile (← setupUnreadableFile)
  testMkRejectsNonDirectoryParent (← setupNonDirectoryParent)
  testMkServerRejectsEmptyPaths certFile keyFile
  testRejectsDirectoryPaths (← setupDirectory) certFile keyFile
  testAppendsNoteToReadableNonRegularFile certFile
