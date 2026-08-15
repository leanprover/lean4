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

-- Three distinct certificates in one file, the shape of a real CA bundle.
def testBundlePEM : String := testCertPEM ++ testWildcardCertPEM ++ testMultiSANCertPEM

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

-- Materializes rejected input on disk for the path-based APIs.
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
  let _clientCtx ← Context.Client.mkFromPEM "" true

-- `verifyPeer := false` succeeds without parsing the CA material, even for a real bundle.
def testMkFromPEMNoVerify (certFile : String) : IO Unit := do
  let caPEM ← IO.FS.readFile certFile
  let _clientCtx ← Context.Client.mkFromPEM caPEM false

-- A bundle of several distinct certificates is loaded in full: every certificate in the PEM becomes
-- a trust anchor, not just the first one.
def testMkFromPEMAcceptsBundle : IO Unit := do
  let _clientCtx ← Context.Client.mkFromPEM testBundlePEM true

def testMkAcceptsBundleFile (bundleFile : String) : IO Unit := do
  let _clientCtx ← Context.Client.mk bundleFile true

-- Repeated certificates are skipped instead of failing, so a bundle that overlaps the system trust
-- anchors (or repeats itself) still yields a usable context.
def testMkFromPEMAcceptsDuplicates : IO Unit := do
  let _clientCtx ← Context.Client.mkFromPEM (testCertPEM ++ testCertPEM) true

def testMkAcceptsDuplicatesInFile (dupFile : String) : IO Unit := do
  let _clientCtx ← Context.Client.mk dupFile true

-- Unlike the path-based APIs, `mkFromPEM` hands OpenSSL an explicit length rather than a C string,
-- so a NUL byte is data (here: trailing junk after a complete certificate) and not an error.
def testMkFromPEMAcceptsNulBytes : IO Unit := do
  let _clientCtx ← Context.Client.mkFromPEM (testCertPEM.push '\x00') true

def testMkFromPEMRejectsGarbage : IO Unit := do
  assertErrorMessage "garbage PEM"
    (malformedPEMError "the given CA PEM string contains no certificates")
    (discard <| Context.Client.mkFromPEM "not a certificate at all" true)

def testMkNoVerifyIgnoresCorruptCAFile (corruptFile : String) : IO Unit := do
  let _clientCtx ← Context.Client.mk corruptFile false

def testMkFromPEMRejectsEmptyBlock : IO Unit := do
  assertErrorMessage "PEM without certificates"
    (malformedPEMError "could not read PEM CA certificates from the given string")
    (discard <| Context.Client.mkFromPEM "-----BEGIN CERTIFICATE-----\n-----END CERTIFICATE-----\n" true)

def testMkFromPEMRejectsCorruptCert : IO Unit := do
  assertErrorMessage "one-bit-flipped CA PEM"
    (malformedPEMError "could not read PEM CA certificates from the given string")
    (discard <| Context.Client.mkFromPEM testCorruptCertPEM true)

-- Text with no PEM armour at all parses to an empty bundle rather than failing to parse, so it is
-- reported as "no certificates" — the same way `mkFromPEM` reports the same bytes.
def testMkRejectsMalformedCAFile (junkFile : String) : IO Unit := do
  assertErrorMessage "malformed CA file"
    (malformedFileError junkFile "the CA file contains no certificates")
    (discard <| Context.Client.mk junkFile true)

def testMkRejectsCorruptCAFile (corruptFile : String) : IO Unit := do
  assertErrorMessage "one-bit-flipped CA file"
    (malformedFileError corruptFile "could not read PEM CA certificates")
    (discard <| Context.Client.mk corruptFile true)

def testMkRejectsMissingCAFile : IO Unit := do
  assertErrorMessage "missing CA file"
    (missingFileError "/nonexistent/path/to/ca.pem")
    (discard <| Context.Client.mk "/nonexistent/path/to/ca.pem" true)

def testMkServerRejectsMissingCert (keyFile : String) : IO Unit := do
  assertErrorMessage "missing server cert"
    (missingFileError "/nonexistent/cert.pem")
    (discard <| Context.Server.mk "/nonexistent/cert.pem" keyFile)

def testMkServerRejectsMissingKey (certFile : String) : IO Unit := do
  assertErrorMessage "missing server key"
    (missingFileError "/nonexistent/key.pem")
    (discard <| Context.Server.mk certFile "/nonexistent/key.pem")

def testMkServerRejectsMalformedKey (certFile junkFile : String) : IO Unit := do
  assertErrorMessage "malformed server key"
    (malformedFileError junkFile "could not read an unencrypted PEM private key")
    (discard <| Context.Server.mk certFile junkFile)

def testMkServerRejectsCertAsKey (certFile : String) : IO Unit := do
  assertErrorMessage "certificate used as server key"
    (malformedFileError certFile "could not read an unencrypted PEM private key")
    (discard <| Context.Server.mk certFile certFile)

def testMkServerRejectsMalformedCert (junkFile keyFile : String) : IO Unit := do
  assertErrorMessage "malformed server cert"
    (malformedFileError junkFile "could not read a PEM certificate chain")
    (discard <| Context.Server.mk junkFile keyFile)

def testMkServerRejectsCorruptCert (corruptFile keyFile : String) : IO Unit := do
  assertErrorMessage "one-bit-flipped server cert"
    (malformedFileError corruptFile "could not read a PEM certificate chain")
    (discard <| Context.Server.mk corruptFile keyFile)

def testMkServerRejectsSwappedFiles (certFile keyFile : String) : IO Unit := do
  assertErrorMessage "swapped server cert/key"
    (malformedFileError keyFile "could not read a PEM certificate chain")
    (discard <| Context.Server.mk keyFile certFile)

def testMkServerRejectsMismatchedKey (certFile key2File : String) : IO Unit := do
  assertErrorMessage "server key from a different pair"
    (malformedFileError key2File "the private key does not match the certificate")
    (discard <| Context.Server.mk certFile key2File)

-- A key of a different algorithm than the certificate lands in an unused slot of the context, so
-- `SSL_CTX_use_PrivateKey_file` accepts it without ever comparing the two; only the separate
-- `SSL_CTX_check_private_key` rejects it.
def testMkServerRejectsCrossAlgorithmKey (certFile ecKeyFile : String) : IO Unit := do
  assertErrorMessage "EC server key against an RSA certificate"
    (malformedFileError ecKeyFile "the private key does not match the certificate")
    (discard <| Context.Server.mk certFile ecKeyFile)

-- Encrypted keys are unsupported. The point of this test is as much the absence of output as the
-- error itself: with no password callback installed OpenSSL prompts for the passphrase on the
-- terminal, which blocks when one is attached and pollutes the test output when one is not.
def testMkServerRejectsEncryptedKey (certFile encKeyFile : String) : IO Unit := do
  assertErrorMessage "passphrase-protected server key"
    (malformedFileError encKeyFile "could not read an unencrypted PEM private key")
    (discard <| Context.Server.mk certFile encKeyFile)

-- An empty passphrase still counts as encrypted. A password callback that reports a zero-length
-- passphrase instead of a failure decrypts this key and accepts it.
def testMkServerRejectsEmptyPassphraseKey (certFile emptyPwKeyFile : String) : IO Unit := do
  assertErrorMessage "server key encrypted under an empty passphrase"
    (malformedFileError emptyPwKeyFile "could not read an unencrypted PEM private key")
    (discard <| Context.Server.mk certFile emptyPwKeyFile)

def testMkServerRejectsNulInCert (keyFile : String) : IO Unit := do
  let certPath := "cert\x00.pem"

  assertErrorMessage "NUL byte in server cert path"
    (nulByteError certPath)
    (discard <| Context.Server.mk certPath keyFile)

def testMkServerRejectsNulInKey (certFile : String) : IO Unit := do
  let keyPath := "key\x00.pem"

  assertErrorMessage "NUL byte in server key path"
    (nulByteError keyPath)
    (discard <| Context.Server.mk certFile keyPath)

-- The CA path is checked before `verifyPeer`, so a NUL is rejected even when the file would never
-- have been opened.
def testMkRejectsNulInCAFile : IO Unit := do
  let caPath := "ca\x00.pem"

  assertErrorMessage "NUL byte in CA path"
    (nulByteError caPath)
    (discard <| Context.Client.mk caPath true)

  assertErrorMessage "NUL byte in CA path without verification"
    (nulByteError caPath)
    (discard <| Context.Client.mk caPath false)

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
    (discard <| Context.Server.mk encCertFile keyFile)

def testMkRejectsEncryptedCertCAFile (encCertFile : String) : IO Unit := do
  assertErrorMessage "encrypted CA certificate file"
    (malformedFileError encCertFile "could not read PEM CA certificates")
    (discard <| Context.Client.mk encCertFile true)

def testMkFromPEMRejectsEncryptedCert : IO Unit := do
  assertErrorMessage "encrypted CA certificate string"
    (malformedPEMError "could not read PEM CA certificates from the given string")
    (discard <| Context.Client.mkFromPEM testEncryptedCertPEM true)

-- A CA bundle is required to contain at least one certificate. `SSL_CTX_load_verify_locations`
-- reports success for a file holding only a key, which would leave the trust store silently
-- unchanged, so the count is checked explicitly.
def testMkRejectsCertlessCAFile (keyFile : String) : IO Unit := do
  assertErrorMessage "CA file holding only a private key"
    (malformedFileError keyFile "the CA file contains no certificates")
    (discard <| Context.Client.mk keyFile true)

def testMkFromPEMRejectsCertlessPEM : IO Unit := do
  assertErrorMessage "CA string holding only a private key"
    (malformedPEMError "the given CA PEM string contains no certificates")
    (discard <| Context.Client.mkFromPEM testKeyPEM true)

-- Non-certificate entries in a bundle are skipped rather than rejected. A *traditional* RSA key is
-- the case that matters: it yields a parsed entry carrying no certificate, unlike the PKCS#8 form
-- which is dropped before that point.
def testMkFromPEMSkipsTraditionalKey : IO Unit := do
  let _clientCtx ← Context.Client.mkFromPEM (testTraditionalKeyPEM ++ testCertPEM) true
  let _clientCtx2 ← Context.Client.mkFromPEM (testCertPEM ++ testTraditionalKeyPEM) true

def testMkFromPEMRejectsTraditionalKeyOnly : IO Unit := do
  assertErrorMessage "traditional RSA key with no certificate"
    (malformedPEMError "the given CA PEM string contains no certificates")
    (discard <| Context.Client.mkFromPEM testTraditionalKeyPEM true)

/-!
`mkFromPEM` hands OpenSSL an explicit length rather than a C string, so a NUL is data and everything
after it is still parsed. Appending a NUL to a complete certificate would pass either way, so these
put material the parser must still reach *after* the NUL.
-/

def testMkFromPEMReadsPastNul : IO Unit := do
  let _clientCtx ← Context.Client.mkFromPEM ("\x00\n" ++ testCertPEM) true

def testMkFromPEMParsesPastNul : IO Unit := do
  assertErrorMessage "corrupt certificate after a NUL byte"
    (malformedPEMError "could not read PEM CA certificates from the given string")
    (discard <| Context.Client.mkFromPEM (testCertPEM ++ "\x00\n" ++ testCorruptCertPEM) true)

-- The whole chain is loaded, not just the leaf, so a corrupt certificate in a later position is
-- still rejected. This is the observable difference between `SSL_CTX_use_certificate_chain_file`
-- and `SSL_CTX_use_certificate_file`.
def testMkServerRejectsCorruptChainMember (chainFile keyFile : String) : IO Unit := do
  assertErrorMessage "corrupt intermediate in the server chain"
    (malformedFileError chainFile "could not read a PEM certificate chain")
    (discard <| Context.Server.mk chainFile keyFile)

-- Building a context parses certificates; it does not check their validity period. An expired
-- certificate is therefore accepted here and only rejected at handshake time.
def testAcceptsExpiredCert (expiredFile keyFile : String) : IO Unit := do
  let _serverCtx ← Context.Server.mk expiredFile keyFile
  let _clientCtx ← Context.Client.mkFromPEM testExpiredCertPEM true

/-!
The path is reported with the failure whenever the `IO.Error` constructor has room for it. These
also pin the errno itself, which is what would catch a platform decoding an OS error code through
the wrong table.
-/

-- Skipped when the permission bits do not bite, which is the case for a privileged user.
def testMkRejectsUnreadableCAFile (unreadableFile : String) : IO Unit := do
  if (← (IO.FS.readFile unreadableFile).toBaseIO).isOk then
    return

  assertErrorMessage "CA file with no read permission"
    s!"permission denied (error code: 13)\n  file: {unreadableFile}"
    (discard <| Context.Client.mk unreadableFile true)

def testMkRejectsNonDirectoryParent (notADirPath : String) : IO Unit := do
  assertErrorMessage "CA path whose parent is a regular file"
    s!"inappropriate type (error code: 20, not a directory)\n  file: {notADirPath}"
    (discard <| Context.Client.mk notADirPath true)

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

-- NUL is data, not a terminator.
#eval do
  testMkFromPEMReadsPastNul
  testMkFromPEMParsesPastNul

#eval do
  let (certFile, keyFile) ← setupTestCerts

  testMkServerRejectsCorruptChainMember (← setupCorruptChain) keyFile
  testAcceptsExpiredCert (← setupExpiredCert) keyFile
  testMkClientFromPEM certFile

-- OS-level failures keep the path and the real errno.
#eval do
  testMkRejectsUnreadableCAFile (← setupUnreadableFile)
  testMkRejectsNonDirectoryParent (← setupNonDirectoryParent)
