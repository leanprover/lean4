import Std.Internal.SSL
import Std.Async.System
import Lean

/-!
Tests for `Std.Internal.SSL.Context`: TLS context creation and configuration. Nothing here performs
a handshake, so what a context trusts is only observable through what it refuses to build; session
and socket behaviour are exercised in separate test files.
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

-- The key of `intermediate.pem`, so it matches none of the certificates above and is only good for
-- provoking a key/cert mismatch.
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

-- Signed by `cert.pem` rather than by itself, so it is a CA that no chain can terminate at. It is
-- the only fixture here whose issuer differs from its subject.
def testIntermediateCertPEM : String := include_cert% "async_ssl_certs/intermediate.pem"

-- A CRL: the non-certificate bundle entry that is not a private key. It is what separates "this
-- bundle holds no certificates" from "this bundle could not be read".
def testCRLPEM : String := include_cert% "async_ssl_certs/crl.pem"

-- `intermediate.pem` carrying explicit trust for TLS server authentication, which lets it anchor a
-- chain although it is not self-signed.
def testTrustedIntermediatePEM : String := include_cert% "async_ssl_certs/trustedintermediate.pem"

-- `cert.pem` carrying an explicit rejection for TLS server authentication, which stops it anchoring
-- a chain although it is self-signed.
def testRejectedCertPEM : String := include_cert% "async_ssl_certs/rejectedcert.pem"

-- A key that parses but whose algorithm cannot sign, so no TLS certificate can use it.
def testX25519KeyPEM : String := include_cert% "async_ssl_certs/x25519key.pem"

-- Three distinct certificates in one file, the shape of a real CA bundle.
def testBundlePEM : String := testCertPEM ++ testWildcardCertPEM ++ testMultiSANCertPEM

/-!
Every file the `PEM.file` cases need, written into a temporary directory that is removed once the
block using it finishes. The in-memory constants above are the same material; a fixture exists only
where a test needs a *path*.
-/

structure Fixtures where
  cert : String
  key : String
  /-- Matches no certificate used here, so pairing it with `cert` is a key/certificate mismatch. -/
  unrelatedKey : String
  ecKey : String
  encKey : String
  emptyPwKey : String
  encCert : String
  expired : String
  weak : String
  intermediate : String
  /-- Text with no PEM armour at all. -/
  junk : String
  corrupt : String
  /-- A valid leaf followed by a corrupt second certificate: a chain whose *intermediate* is bad. -/
  chain : String
  empty : String
  dir : String
  unreadable : String
  /-- A path that treats a regular file as if it were a directory, which the OS refuses. -/
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

/--
Runs `k` against a fresh fixture directory, removed afterwards even when `k` throws. `secret.pem` is
unreadable by design, but removing it only needs write permission on the directory holding it.
-/
def withFixtures (k : Fixtures → IO α) : IO α :=
  IO.FS.withTempDir fun root => do k (← mkFixturesIn root)

-- Asserts that an IO action fails with exactly `expected` as its message.
def assertErrorMessage (label expected : String) (act : IO Unit) : IO Unit := do
  match ← act.toBaseIO with
  | .ok _ => throw <| IO.userError s!"{label}: expected failure, but it succeeded"
  | .error e =>
    let actual := toString e
    unless actual == expected do
      throw <| IO.userError s!"{label}:\nexpected error: {expected}\nactual error:   {actual}"

-- For a failure whose exact wording depends on the platform's C library. The set is spelled out so an
-- unexpected *third* message still fails the test.
def assertErrorMessageOneOf (label : String) (expected : List String) (act : IO Unit) : IO Unit := do
  match ← act.toBaseIO with
  | .ok _ => throw <| IO.userError s!"{label}: expected failure, but it succeeded"
  | .error e =>
    let actual := toString e
    unless expected.contains actual do
      throw <| IO.userError s!"{label}:\nexpected one of:\n\
        {String.intercalate "\n  --- or ---\n" expected}\nactual error:   {actual}"

-- A file that cannot be opened is reported with the `errno` the open failed with, on the offending
-- path.
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

/-!
The CA loader reports one message per failure regardless of where the material came from: the
`file:` field the error already carries is what says which source it was.
-/

def caUnreadable : String := "could not read PEM CA certificates"

def caNoCerts : String := "the CA material contains no certificates"

def caNoAnchor : String :=
  "the CA material holds no certificate a TLS server chain can terminate in (supply the root, or \
    allow partial chains to anchor at an intermediate)"

/--
Whether the host supplies platform trust anchors. A Nix sandbox or a container without
`ca-certificates` has none, and a default context is then refused by design, so the few tests that
need one are skipped there. That is only expected where the anchors come from files: macOS and
Windows always have a platform store, so a failure there, like any other failure, fails the test.
-/
def hasSystemRoots : IO Bool := do
  match ← (discard <| Context.Client.mk).toBaseIO with
  | .ok _ => return true
  | .error e =>
    let fileBased := !System.Platform.isOSX && !System.Platform.isWindows
    if fileBased && (toString e).startsWith "failed to load system trust store" then
      return false
    throw e

-- Context creation and configuration (smoke test).
def testContextCreation (f : Fixtures) : IO Unit := do
  let _serverCtx ← Context.Server.mk { cert := .file f.cert, key := .file f.key }

  -- Empty CA with `verifyPeer := false` disables verification without parsing any CA material.
  let _clientCtx ← Context.Client.mk { verifyPeer := false }

  -- Non-empty CA file with `verifyPeer := true` exercises the additive trust path: the system
  -- roots plus the supplied CA.
  let _clientCtx2 ← Context.Client.mk { ca := some (.file f.cert) }

  -- A non-empty CA path with `verifyPeer := false` is accepted, but the CA file is not parsed.
  let _clientCtx3 ← Context.Client.mk { ca := some (.file f.cert), verifyPeer := false }

  -- Defaults: no CA file, peer verification against the system trust anchors.
  if ← hasSystemRoots then
    discard <| Context.Client.mk

  -- The same anchors supplied in memory rather than by path.
  let _clientCtx5 ← Context.Client.mk { ca := some (.text testCertPEM) }

/-!
`trustSystemRoots := false` narrows the store to the supplied CA, which is what pinning against a
private authority needs. The store a context starts with is empty, so excluding the platform anchors
without naming a CA would leave nothing to verify against — a context that could never complete a
handshake. That is refused at construction instead of at connection time.
-/

def noAnchorsError : String :=
  malformedPEMError "no trust anchors: peer verification is on, the platform trust anchors are \
    excluded, and no CA certificate was given"

def testPinnedToSuppliedCA (f : Fixtures) : IO Unit := do
  let _clientCtx ← Context.Client.mk { ca := some (.file f.cert), trustSystemRoots := false }
  let _clientCtx2 ← Context.Client.mk { ca := some (.text testCertPEM), trustSystemRoots := false }
  let _clientCtx3 ← Context.Client.mk { ca := some (.text testBundlePEM), trustSystemRoots := false }

def testPinningRejectsEmptyCA : IO Unit := do
  assertErrorMessage "pinned with no CA at all" noAnchorsError
    (discard <| Context.Client.mk { trustSystemRoots := false })

-- `ca := some` is a claim that anchors were supplied, so empty material is a bundle that holds no
-- certificate rather than an absent one. That is a different diagnosis from the case above, and the
-- more specific of the two.
def testPinningRejectsEmptyCAMaterial : IO Unit := do
  assertErrorMessage "pinned to an empty CA string" (malformedPEMError caNoCerts)
    (discard <| Context.Client.mk { ca := some (.text ""), trustSystemRoots := false })

/-!
A trust anchor has to be a certificate chain building can terminate at, which by default means a
self-signed one. Pinning to nothing but intermediates therefore describes a context that could never
verify anything; `allowPartialChain` is what makes it verify, and without it the configuration is
refused where the mistake is rather than at every handshake.
-/

def testPinningRejectsIntermediateOnly (f : Fixtures) : IO Unit := do
  assertErrorMessage "pinned to an intermediate PEM" (malformedPEMError caNoAnchor)
    (discard <| Context.Client.mk
      { ca := some (.text testIntermediateCertPEM), trustSystemRoots := false })

  assertErrorMessage "pinned to an intermediate CA file"
    (malformedFileError f.intermediate caNoAnchor)
    (discard <| Context.Client.mk { ca := some (.file f.intermediate), trustSystemRoots := false })

-- `allowPartialChain` is the opt-in that makes an intermediate anchor a chain, so the same material
-- is accepted once it is set.
def testPinningToIntermediateWithPartialChain (f : Fixtures) : IO Unit := do
  let _clientCtx ← Context.Client.mk
    { ca := some (.text testIntermediateCertPEM), trustSystemRoots := false,
      allowPartialChain := true }

  let _clientCtx2 ← Context.Client.mk
    { ca := some (.file f.intermediate), trustSystemRoots := false, allowPartialChain := true }

-- A bundle pairing the root with the intermediates beneath it terminates at the root, so the order
-- the two appear in does not matter.
def testPinningAcceptsRootWithIntermediate : IO Unit := do
  let _clientCtx ← Context.Client.mk
    { ca := some (.text (testIntermediateCertPEM ++ testCertPEM)), trustSystemRoots := false }

  let _clientCtx2 ← Context.Client.mk
    { ca := some (.text (testCertPEM ++ testIntermediateCertPEM)), trustSystemRoots := false }

-- Alongside the platform anchors an intermediate is redundant rather than fatal, so the check fires
-- only where the supplied material is the sole source of anchors — which it also is on a host whose
-- platform supplies none.
def testIntermediateAllowedBesideSystemRoots : IO Unit := do
  if ← hasSystemRoots then
    discard <| Context.Client.mk { ca := some (.text testIntermediateCertPEM) }
  else
    assertErrorMessage "intermediate on a host without platform anchors"
      (malformedPEMError caNoAnchor)
      (discard <| Context.Client.mk { ca := some (.text testIntermediateCertPEM) })

/-!
Self-signed is the default notion of an anchor, not the only one: a `TRUSTED CERTIFICATE` block carries
explicit trust settings that OpenSSL consults first. Trust for TLS servers makes an intermediate an
anchor on its own, and a rejection unmakes a self-signed root.
-/

def testPinningToExplicitlyTrustedIntermediate : IO Unit := do
  let _clientCtx ← Context.Client.mk
    { ca := some (.text testTrustedIntermediatePEM), trustSystemRoots := false }

def testPinningRejectsExplicitlyRejectedRoot : IO Unit := do
  assertErrorMessage "pinned to a root rejected for TLS servers" (malformedPEMError caNoAnchor)
    (discard <| Context.Client.mk { ca := some (.text testRejectedCertPEM), trustSystemRoots := false })

  -- The store keeps the first copy of a repeated certificate, so a plain copy behind the rejected one
  -- anchors nothing either. The reverse order keeps the plain copy, which does.
  assertErrorMessage "rejected root repeated as a plain copy" (malformedPEMError caNoAnchor)
    (discard <| Context.Client.mk
      { ca := some (.text (testRejectedCertPEM ++ testCertPEM)), trustSystemRoots := false })

  let _clientCtx ← Context.Client.mk
    { ca := some (.text (testCertPEM ++ testRejectedCertPEM)), trustSystemRoots := false }

-- With verification off there is no store to be empty, so excluding the platform anchors is not a
-- contradiction and `trustSystemRoots` is simply ignored.
def testPinningIgnoredWithoutVerification : IO Unit := do
  let _clientCtx ← Context.Client.mk { verifyPeer := false, trustSystemRoots := false }

-- Supplied CA material still has to yield a certificate. These reach the ordinary bundle-loading
-- failures rather than the "no trust anchors" one, which is what pins the check to the *absence* of
-- CA material rather than to it being unusable.
def testPinningStillValidatesCA (f : Fixtures) : IO Unit := do
  assertErrorMessage "pinned to a malformed CA file" (malformedFileError f.junk caNoCerts)
    (discard <| Context.Client.mk { ca := some (.file f.junk), trustSystemRoots := false })

  assertErrorMessage "pinned to a CA string with no certificates" (malformedPEMError caNoCerts)
    (discard <| Context.Client.mk
      { ca := some (.text "not a certificate at all"), trustSystemRoots := false })

/-!
Server credentials may be supplied in memory rather than by path, for a certificate that comes from
a secret manager or is embedded in the binary. The two sources meet in a single loader as soon as
the material is open, so the cases below cover what is particular to `PEM.text`: no path to name in
a failure, and no NUL restriction. The diagnoses themselves are exercised through `PEM.file`.
-/

def testMkServerFromMemory (f : Fixtures) : IO Unit := do
  let _serverCtx ← Context.Server.mk { cert := .text testCertPEM, key := .text testKeyPEM }

  -- The two sources are independent, so a file certificate pairs with an in-memory key and back.
  let _serverCtx2 ← Context.Server.mk { cert := .file f.cert, key := .text testKeyPEM }
  let _serverCtx3 ← Context.Server.mk { cert := .text testCertPEM, key := .file f.key }

  -- The whole chain is loaded from memory too, not just the leaf.
  let _serverCtx4 ← Context.Server.mk
    { cert := .text (testCertPEM ++ testWildcardCertPEM), key := .text testKeyPEM }

-- In-memory failures report the same diagnoses as the path-based ones, without a path attached.
-- One unreadable case and one mismatch case pin both error shapes.
def testMkServerFromMemoryErrors : IO Unit := do
  assertErrorMessage "malformed in-memory certificate"
    (malformedPEMError "could not read a PEM certificate chain")
    (discard <| Context.Server.mk { cert := .text "this is not pem\n", key := .text testKeyPEM })

  assertErrorMessage "mismatched in-memory key"
    (malformedPEMError "the private key does not match the certificate")
    (discard <| Context.Server.mk { cert := .text testCertPEM, key := .text testUnrelatedKeyPEM })

-- A path cannot carry a NUL, but in-memory material is read with a length, so it can.
def testMkServerFromMemoryAcceptsNul : IO Unit := do
  let _serverCtx ← Context.Server.mk
    { cert := .text (testCertPEM.push '\x00'), key := .text testKeyPEM }

-- Repeated certificates are skipped instead of failing, so a bundle that overlaps the system trust
-- anchors (or repeats itself) still yields a usable context. That the certificates behind the first
-- are loaded at all is what `testPinningAcceptsRootWithIntermediate` shows.
def testMkFromPEMAcceptsBundle : IO Unit := do
  let _clientCtx ← Context.Client.mk { ca := some (.text testBundlePEM) }
  let _clientCtx2 ← Context.Client.mk { ca := some (.text (testBundlePEM ++ testCertPEM)) }

-- Unlike `PEM.file`, `PEM.text` hands OpenSSL an explicit length rather than a C string,
-- so a NUL byte is data (here: trailing junk after a complete certificate) and not an error.
def testMkFromPEMAcceptsNulBytes : IO Unit := do
  let _clientCtx ← Context.Client.mk { ca := some (.text (testCertPEM.push '\x00')) }

def testMkNoVerifyIgnoresCorruptCAFile (f : Fixtures) : IO Unit := do
  let _clientCtx ← Context.Client.mk { ca := some (.file f.corrupt), verifyPeer := false }

def testMkFromPEMRejectsEmptyBlock : IO Unit := do
  assertErrorMessage "PEM without certificates" (malformedPEMError caUnreadable)
    (discard <| Context.Client.mk
      { ca := some (.text "-----BEGIN CERTIFICATE-----\n-----END CERTIFICATE-----\n") })

-- Text with no PEM armour at all parses to an empty bundle rather than failing to parse, so it is
-- reported as "no certificates" rather than as unreadable.
def testMkRejectsMalformedCAFile (f : Fixtures) : IO Unit := do
  assertErrorMessage "malformed CA file" (malformedFileError f.junk caNoCerts)
    (discard <| Context.Client.mk { ca := some (.file f.junk) })

def testMkRejectsCorruptCAFile (f : Fixtures) : IO Unit := do
  assertErrorMessage "one-bit-flipped CA file" (malformedFileError f.corrupt caUnreadable)
    (discard <| Context.Client.mk { ca := some (.file f.corrupt) })

def testMkRejectsMissingCAFile : IO Unit := do
  assertErrorMessage "missing CA file"
    (missingFileError "/nonexistent/path/to/ca.pem")
    (discard <| Context.Client.mk { ca := some (.file "/nonexistent/path/to/ca.pem") })

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

-- A key that parses but cannot sign is refused for its algorithm, not reported as unreadable.
def testMkServerRejectsUnusableKeyAlgorithm : IO Unit := do
  assertErrorMessage "X25519 server key"
    (malformedPEMError "the private key's algorithm cannot be used for TLS")
    (discard <| Context.Server.mk { cert := .text testCertPEM, key := .text testX25519KeyPEM })

-- A key of a different algorithm than the certificate lands in an unused slot of the context, so
-- `SSL_CTX_use_PrivateKey` accepts it without ever comparing the two; only the separate
-- `SSL_CTX_check_private_key` rejects it.
def testMkServerRejectsCrossAlgorithmKey (f : Fixtures) : IO Unit := do
  assertErrorMessage "EC server key against an RSA certificate"
    (malformedFileError f.ecKey "the private key does not match the certificate")
    (discard <| Context.Server.mk { cert := .file f.cert, key := .file f.ecKey })

/-!
Encrypted PEM material must be rejected outright. A passphrase callback reporting failure is what
prevents OpenSSL falling back to its own callback, which prompts on `/dev/tty` and blocks forever —
a hang that no amount of redirecting stdin escapes. The point of these tests is as much the absence
of output as the error itself. An encrypted *certificate* is decrypted in place while the bundle is
read, so it reaches the callback through a different path than a key does, in each constructor.
-/

def testRejectsEncryptedMaterial (f : Fixtures) : IO Unit := do
  assertErrorMessage "passphrase-protected server key"
    (malformedFileError f.encKey "could not read an unencrypted PEM private key")
    (discard <| Context.Server.mk { cert := .file f.cert, key := .file f.encKey })

  -- An empty passphrase still counts as encrypted. A password callback that reports a zero-length
  -- passphrase instead of a failure decrypts this key and accepts it.
  assertErrorMessage "server key encrypted under an empty passphrase"
    (malformedFileError f.emptyPwKey "could not read an unencrypted PEM private key")
    (discard <| Context.Server.mk { cert := .file f.cert, key := .file f.emptyPwKey })

  assertErrorMessage "encrypted server certificate"
    (malformedFileError f.encCert "could not read a PEM certificate chain")
    (discard <| Context.Server.mk { cert := .file f.encCert, key := .file f.key })

  assertErrorMessage "encrypted CA certificate file"
    (malformedFileError f.encCert caUnreadable)
    (discard <| Context.Client.mk { ca := some (.file f.encCert) })

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
    (discard <| Context.Client.mk { ca := some (.file caPath) })

  -- The CA path is checked before `verifyPeer`, so a NUL is rejected even when the file would never
  -- have been opened.
  assertErrorMessage "NUL byte in CA path without verification" (nulByteError caPath)
    (discard <| Context.Client.mk { ca := some (.file caPath), verifyPeer := false })

/-!
A CA bundle is required to contain at least one certificate. Material holding only non-certificate
entries parses without complaint and would leave the trust store silently unchanged, so the count is
checked explicitly. A *traditional* RSA key is the case that matters among those entries: it yields
a parsed entry carrying no certificate, unlike the PKCS#8 form which is dropped before that point.
A CRL is the other one.
-/

def testMkRejectsCertlessCAFile (f : Fixtures) : IO Unit := do
  assertErrorMessage "CA file holding only a private key" (malformedFileError f.key caNoCerts)
    (discard <| Context.Client.mk { ca := some (.file f.key) })

  -- A zero-byte file has no PEM armour to fail on, so it parses to an empty bundle too.
  assertErrorMessage "zero-byte CA file" (malformedFileError f.empty caNoCerts)
    (discard <| Context.Client.mk { ca := some (.file f.empty) })

def testMkFromPEMRejectsCertlessPEM : IO Unit := do
  assertErrorMessage "traditional RSA key with no certificate" (malformedPEMError caNoCerts)
    (discard <| Context.Client.mk { ca := some (.text testTraditionalKeyPEM) })

  assertErrorMessage "CA string holding only a CRL" (malformedPEMError caNoCerts)
    (discard <| Context.Client.mk { ca := some (.text testCRLPEM) })

-- Non-certificate entries alongside a certificate are skipped rather than rejected.
def testMkFromPEMSkipsNonCertificates : IO Unit := do
  let _clientCtx ← Context.Client.mk { ca := some (.text (testTraditionalKeyPEM ++ testCertPEM)) }
  let _clientCtx2 ← Context.Client.mk { ca := some (.text (testCertPEM ++ testTraditionalKeyPEM)) }
  let _clientCtx3 ← Context.Client.mk { ca := some (.text (testCRLPEM ++ testCertPEM)) }
  let _clientCtx4 ← Context.Client.mk { ca := some (.text (testCertPEM ++ testCRLPEM)) }

/-!
`PEM.text` hands OpenSSL an explicit length rather than a C string, so a NUL does not truncate the
input. It is still junk to the PEM parser, which needs `-----BEGIN` to start a line, so where the
NUL sits decides between three outcomes.
-/

-- Terminated by a newline the NUL is skipped like any other junk line.
def testMkFromPEMReadsPastNul : IO Unit := do
  let _clientCtx ← Context.Client.mk { ca := some (.text ("\x00\n" ++ testCertPEM)) }

-- Sharing a line with the marker, the NUL hides it and that certificate is dropped without an error
-- of its own; only the empty bundle behind it is reported.
def testMkFromPEMDropsCertBehindNul : IO Unit := do
  assertErrorMessage "certificate behind an unterminated NUL" (malformedPEMError caNoCerts)
    (discard <| Context.Client.mk { ca := some (.text ("\x00" ++ testCertPEM)) })

-- Inside the body the NUL corrupts the block, which discards the whole bundle rather than just that
-- certificate.
def testMkFromPEMRejectsNulInsideCert : IO Unit := do
  let split := 200
  assertErrorMessage "NUL inside a certificate body" (malformedPEMError caUnreadable)
    (discard <| Context.Client.mk { ca := some (.text
      ((testCertPEM.take split).toString ++ "\x00" ++ (testCertPEM.drop split).toString)) })

-- The whole chain is loaded, not just the leaf, so a corrupt certificate in a later position is
-- still rejected. This is the observable difference between `SSL_CTX_use_certificate_chain_file`
-- and `SSL_CTX_use_certificate_file`.
def testMkServerRejectsCorruptChainMember (f : Fixtures) : IO Unit := do
  assertErrorMessage "corrupt intermediate in the server chain"
    (malformedFileError f.chain "could not read a PEM certificate chain")
    (discard <| Context.Server.mk { cert := .file f.chain, key := .file f.key })

-- Building a context parses certificates; it does not check their validity period. An expired
-- certificate is therefore accepted here and only rejected at handshake time.
def testAcceptsExpiredCert (f : Fixtures) : IO Unit := do
  let _serverCtx ← Context.Server.mk { cert := .file f.expired, key := .file f.key }
  let _clientCtx ← Context.Client.mk { ca := some (.text testExpiredCertPEM) }

/-!
A certificate can be refused on policy grounds rather than because it could not be read: the TLS
security level turns away an RSA key that is too short. Reporting that as unparsable PEM sends the
reader after a problem their file does not have. Every context runs at security level 2 or above,
which a 512-bit key fails whatever a system crypto policy adds. The weak certificate is paired with an
unrelated key, so a context that did admit it would still fail, but with a different message.
-/

def weakCertError : String :=
  "the certificate is rejected by the TLS security level (key too small or signature digest too weak)"

def testMkServerRejectsWeakCert (f : Fixtures) : IO Unit := do
  assertErrorMessage "512-bit server certificate" (malformedFileError f.weak weakCertError)
    (discard <| Context.Server.mk { cert := .file f.weak, key := .file f.key })

-- The chain behind the leaf is held to the same level, though a server only forwards it.
def testMkServerRejectsWeakChainMember : IO Unit := do
  assertErrorMessage "512-bit certificate behind the leaf" (malformedPEMError weakCertError)
    (discard <| Context.Server.mk
      { cert := .text (testCertPEM ++ testWeakCertPEM), key := .text testKeyPEM })

-- The security level governs the certificate a server presents, not the anchors a client trusts, so
-- the very file rejected above still loads as a CA. This is what pins the diagnosis to the security
-- level rather than to the certificate being malformed.
def testAcceptsWeakCertAsCA (f : Fixtures) : IO Unit := do
  let _clientCtx ← Context.Client.mk { ca := some (.text testWeakCertPEM) }
  let _clientCtx2 ← Context.Client.mk { ca := some (.file f.weak) }

-- Only the *CA* material has a fallback to the platform anchors. The server has none, so an empty
-- path reaches the OS and fails there.
def testMkServerRejectsEmptyPaths (f : Fixtures) : IO Unit := do
  -- `stat("")` is `ENOENT` on POSIX and `EINVAL` on the Windows CRT.
  assertErrorMessageOneOf "empty server cert path"
    [ missingFileError "", malformedFileError "" "could not read a PEM certificate chain" ]
    (discard <| Context.Server.mk { cert := .file "", key := .file f.key })

  assertErrorMessageOneOf "empty server key path"
    [ missingFileError "", malformedFileError "" "could not read an unencrypted PEM private key" ]
    (discard <| Context.Server.mk { cert := .file f.cert, key := .file "" })

/-!
The path is reported with the failure whenever the `IO.Error` constructor has room for it. These
also pin the errno itself, which is what would catch a platform decoding an OS error code through
the wrong table.
-/

-- A path that is opened but yields nothing usable is classified from its mode afterwards, since the
-- open alone does not tell: POSIX `fopen` succeeds on a directory and fails only at the first read.
-- The note is *appended* to the failure OpenSSL actually reported rather than replacing it, because
-- the file type need not be what went wrong — OpenSSL reads a FIFO or a `/dev/fd` entry as happily as
-- a file on disk (a FIFO waits for its writer first), so a mismatched key reached through one still
-- has to say so.
def testRejectsDirectoryPaths (f : Fixtures) : IO Unit := do
  let note := " (the path is not a regular file)"

  assertErrorMessage "directory as server cert"
    (malformedFileError f.dir ("could not read a PEM certificate chain" ++ note))
    (discard <| Context.Server.mk { cert := .file f.dir, key := .file f.key })

  assertErrorMessage "directory as server key"
    (malformedFileError f.dir ("could not read an unencrypted PEM private key" ++ note))
    (discard <| Context.Server.mk { cert := .file f.cert, key := .file f.dir })

  -- Which failure this is depends on the C library. On POSIX `BIO_new_file` opens the directory and
  -- the read that follows yields nothing, so the empty bundle is what gets reported; the Windows CRT
  -- cannot open a directory as a stream at all, so the BIO is null and the path is unreadable instead.
  -- Either way the note has to be appended rather than substituted, or which of the two it was is lost.
  assertErrorMessageOneOf "directory as CA file"
    [ malformedFileError f.dir (caNoCerts ++ note),
      malformedFileError f.dir (caUnreadable ++ note) ]
    (discard <| Context.Client.mk { ca := some (.file f.dir) })

-- A character device is the readable non-regular file: OpenSSL opens `/dev/null` and reads it to
-- completion, so the diagnosis is about what the empty read produced and the file type is only a
-- footnote.
def testAppendsNoteToReadableNonRegularFile (f : Fixtures) : IO Unit := do
  if System.Platform.isWindows then
    return

  assertErrorMessage "character device as CA file"
    (malformedFileError "/dev/null" (caNoCerts ++ " (the path is not a regular file)"))
    (discard <| Context.Client.mk { ca := some (.file "/dev/null") })

  assertErrorMessage "character device as server key"
    (malformedFileError "/dev/null"
      "could not read an unencrypted PEM private key (the path is not a regular file)")
    (discard <| Context.Server.mk { cert := .file f.cert, key := .file "/dev/null" })

-- Skipped when the permission bits do not bite, which is the case for a privileged user.
def testMkRejectsUnreadableCAFile (f : Fixtures) : IO Unit := do
  if (← (IO.FS.readFile f.unreadable).toBaseIO).isOk then
    return

  assertErrorMessage "CA file with no read permission"
    s!"permission denied (error code: 13)\n  file: {f.unreadable}"
    (discard <| Context.Client.mk { ca := some (.file f.unreadable) })

-- A path traversing a regular file is `ENOTDIR` on POSIX; the Windows CRT reports `ENOENT`.
def testMkRejectsNonDirectoryParent (f : Fixtures) : IO Unit := do
  assertErrorMessageOneOf "CA path whose parent is a regular file"
    [ s!"inappropriate type (error code: 20, not a directory)\n  file: {f.nonDirParent}",
      missingFileError f.nonDirParent ]
    (discard <| Context.Client.mk { ca := some (.file f.nonDirParent) })

/-!
`SSL_CERT_FILE` and `SSL_CERT_DIR` add to the platform anchors, so no value they take can leave a
default context unbuildable: not an empty one, not one naming a file removed since, and not one naming
a single private CA. The environment is read afresh for every context, so it can be changed between
constructions. Windows is skipped because libuv sets variables there through the Win32 API, which the
C runtime's `getenv` does not observe.
-/

def withEnv (name value : String) (act : IO Unit) : IO Unit := do
  let old ← IO.getEnv name
  Std.Async.System.setEnvVar name value
  try act finally
    match old with
    | some v => Std.Async.System.setEnvVar name v
    | none => Std.Async.System.unsetEnvVar name

def testCertEnvVarsNeverBreakDefaultContext (f : Fixtures) : IO Unit := do
  if System.Platform.isWindows then
    return

  -- Pinned contexts never read the environment. Pinning to an intermediate alone is refused for want
  -- of an anchor, and the root `SSL_CERT_FILE` names would supply one if it reached the store.
  withEnv "SSL_CERT_FILE" f.cert do
    assertErrorMessage "pinned context beside an anchor in SSL_CERT_FILE"
      (malformedPEMError caNoAnchor)
      (discard <| Context.Client.mk
        { ca := some (.text testIntermediateCertPEM), trustSystemRoots := false })

  if !(← hasSystemRoots) then
    return

  for value in ["", "/nonexistent/ca.pem", f.junk, f.cert] do
    withEnv "SSL_CERT_FILE" value (discard <| Context.Client.mk {})

  for value in ["", "/nonexistent/certs", f.dir] do
    withEnv "SSL_CERT_DIR" value (discard <| Context.Client.mk {})

#eval withFixtures fun f => do
  testContextCreation f
  testMkServerFromMemory f
  testMkServerFromMemoryErrors
  testMkServerFromMemoryAcceptsNul
  testMkFromPEMAcceptsBundle
  testMkFromPEMAcceptsNulBytes

-- Encrypted PEM, in every constructor. A regression here does not fail loudly: it blocks on a
-- passphrase prompt, so keep these ahead of anything that would mask a hang.
#eval withFixtures fun f => do
  testRejectsEncryptedMaterial f

-- Pinning: `trustSystemRoots := false` narrows the store to the supplied CA.
#eval withFixtures fun f => do
  testPinnedToSuppliedCA f
  testPinningRejectsEmptyCA
  testPinningRejectsEmptyCAMaterial
  testPinningIgnoredWithoutVerification
  testPinningStillValidatesCA f

-- A trust anchor must be one a chain can terminate at.
#eval withFixtures fun f => do
  testPinningRejectsIntermediateOnly f
  testPinningToIntermediateWithPartialChain f
  testPinningAcceptsRootWithIntermediate
  testIntermediateAllowedBesideSystemRoots
  testPinningToExplicitlyTrustedIntermediate
  testPinningRejectsExplicitlyRejectedRoot

-- The environment's anchors add to the platform's.
#eval withFixtures fun f => do
  testCertEnvVarsNeverBreakDefaultContext f

-- CA material that cannot be used as a trust anchor.
#eval withFixtures fun f => do
  testMkRejectsMissingCAFile
  testMkRejectsMalformedCAFile f
  testMkRejectsCorruptCAFile f
  testMkNoVerifyIgnoresCorruptCAFile f
  testMkFromPEMRejectsEmptyBlock
  testMkRejectsCertlessCAFile f
  testMkFromPEMRejectsCertlessPEM
  testMkFromPEMSkipsNonCertificates

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
  testAppendsNoteToReadableNonRegularFile f
