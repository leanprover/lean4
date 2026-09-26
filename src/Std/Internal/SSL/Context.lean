/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module
prelude
public import Init.System.IO

/-!
TLS contexts. A context holds what every connection made from it shares: the certificate and key it
presents, the certificates it trusts, and the protocol settings. Create one context and reuse it for
many connections. It cannot be changed after creation and can be shared between threads.

```lean
-- A client that trusts the system's root certificates.
let client ← Context.Client.mk

-- A client that trusts only your own CA.
let pinned ← Context.Client.mk { trust := .only #[.file "ca.pem"] }

-- A server.
let server ← Context.Server.mk { cert := .file "cert.pem", key := .file "key.pem" }

-- A server that requires a client certificate issued by your CA (mutual TLS).
let mtls ← Context.Server.mk
  { cert := .file "cert.pem", key := .file "key.pem",
    clientAuth := .requireAndVerify #[.file "clients-ca.pem"] }
```

Files are read when the context is created, so a renewed certificate needs a new context.

## Security settings

Every context requires TLS 1.2 or later. TLS 1.2 connections only use ECDHE key exchange with
AES-GCM or ChaCha20-Poly1305; TLS 1.3 uses its three standard cipher suites. RSA keys must be at
least 2048 bits. Session resumption, compression and renegotiation are off, and encrypted keys are
refused rather than prompting for a passphrase.

When Lean uses the system's OpenSSL, that library's configuration can make these settings stricter
but not looser. If it leaves no TLS version or cipher suite these settings allow, creating a context
fails.

## Errors

* `invalidArgument`: the configuration or the PEM material can't be used. The error names the file
  when the material came from one.
* `noSuchThing`: a client trusting the system has no certificates to trust: the system has none,
  or `SSL_CERT_FILE` and `SSL_CERT_DIR` name none.
* `unsupportedOperation`: the system's OpenSSL configuration leaves no TLS version or cipher suite
  these settings allow, or this build of Lean has no TLS support.
* `userError`: OpenSSL failed for some other reason.
* Errors from reading a file are those of `IO.FS.readBinFile`.

## Platform notes

With `trust := .system`, a client trusts:

* macOS: the certificates the system trusts, with the system's own checks, such as Keychain trust
  settings, Certificate Transparency and limits on certificate lifetime.
* Windows: the certificates the system trusts, with the system's own checks, such as the
  `Disallowed` store and the uses each root is trusted for. A root Windows trusts but hasn't
  installed yet is downloaded.
* Linux and others: the distribution's certificate bundle and certificate directories. A Lean build
  that uses the system's OpenSSL also reads OpenSSL's default certificate locations.

Missing intermediate certificates are never downloaded: the server has to send them, or they must be
listed as trusted.

If `SSL_CERT_FILE` or `SSL_CERT_DIR` is set, the certificates they name are trusted instead of the
system's, on every platform. Files that hold no certificate are skipped. `SSL_CERT_FILE` names a PEM bundle; `SSL_CERT_DIR` is a list of
directories, separated by `:` (`;` on Windows), whose files are all read. Both are ignored in
set-user-ID and set-group-ID programs.

Lean does not check whether a certificate has been revoked.
-/

public section

namespace Std.Internal.SSL

/--
PEM-encoded certificates or keys.
-/
inductive PEM where

  /--
  The contents of the file at `path`.
  -/
  | file (path : System.FilePath)

  /--
  The PEM text itself.
  -/
  | text (contents : String)

/--
A certificate and the private key that goes with it.
-/
structure Credentials where
  /--
  The certificate, followed by the intermediate certificates the peer needs to reach a root.
  -/
  cert : PEM
  /--
  The private key for `cert`. It must not be encrypted.
  -/
  key : PEM

/--
A TLS protocol version.
-/
inductive Version where
  /-- TLS 1.2. -/
  | tls12
  /-- TLS 1.3. -/
  | tls13
  deriving Repr, DecidableEq

/--
PEM bytes as the runtime takes them, with the file they came from so that errors can name it.
-/
private structure LoadedPEM where
  bytes : ByteArray
  path? : Option System.FilePath

private def PEM.load : PEM → IO LoadedPEM
  | .text contents =>
    return { bytes := contents.toUTF8, path? := none }
  | .file path => do
    let bytes ← try IO.FS.readBinFile path catch
      | .inappropriateType none code details =>
        throw <| .inappropriateType (some path.toString) code details
      | e =>
        throw e
    return { bytes, path? := some path }

private opaque ContextServerImpl : NonemptyType.{0}

/--
Server-side TLS context.
-/
def Context.Server : Type := ContextServerImpl.type

instance : Nonempty Context.Server := ContextServerImpl.property

private opaque ContextClientImpl : NonemptyType.{0}

/--
Client-side TLS context.
-/
def Context.Client : Type := ContextClientImpl.type

instance : Nonempty Context.Client := ContextClientImpl.property

namespace Context.Server

/--
Whether a server asks clients for a certificate, and what it does with one.
-/
inductive ClientAuth where
  /--
  Don't ask for a certificate.
  -/
  | none
  /--
  Ask for a certificate, but accept a connection without one and don't verify one that is sent.
  -/
  | request
  /--
  Require a certificate, but don't verify it.
  -/
  | requireAny
  /--
  Verify a certificate against these CAs if the client sends one. It must not be empty.
  -/
  | verifyIfGiven (ca : Array PEM)
  /--
  Require a certificate and verify it against these CAs. It must not be empty.
  -/
  | requireAndVerify (ca : Array PEM)

/--
What a server presents and accepts.
-/
structure Config where
  /--
  The server's certificate, followed by the intermediate certificates clients need to reach a root.
  -/
  cert : PEM
  /--
  The private key for `cert`. It must not be encrypted.
  -/
  key : PEM
  /--
  Whether to ask clients for a certificate. When verifying one, any of the listed CA certificates
  can end a chain, not only a root, and their names are sent to help the client pick a certificate.
  -/
  clientAuth : ClientAuth := .none
  /--
  The lowest TLS version to accept.
  -/
  minVersion : Version := .tls12
  /--
  The highest TLS version to accept.
  -/
  maxVersion : Version := .tls13

@[extern "lean_ssl_ctx_mk_server"]
private opaque mkImpl (cert key : @& LoadedPEM) (clientAuth : @& ClientAuth) (clientCA : @& Array LoadedPEM)
    (minVersion maxVersion : Version) : IO Context.Server

/--
Creates a server context. Fails if the key doesn't match the certificate, if either can't be read,
or if `clientAuth` verifies certificates against an empty list.

An expired certificate is accepted here and rejected by clients during the handshake.
-/
def mk (cfg : Config) : IO Context.Server := do
  let clientCA ← match cfg.clientAuth with
    | .verifyIfGiven ca | .requireAndVerify ca => ca.mapM PEM.load
    | _ => pure #[]
  mkImpl (← cfg.cert.load) (← cfg.key.load) cfg.clientAuth clientCA cfg.minVersion cfg.maxVersion

end Server

namespace Client

/--
Which server certificates a client accepts.
-/
inductive Trust where
  /--
  Certificates issued by the system's trusted CAs or by one of `extra`. See the platform notes in the
  module documentation.
  -/
  | system (extra : Array PEM := #[])
  /--
  Only certificates issued by one of these CAs. It must not be empty.
  -/
  | only (ca : Array PEM)
  /--
  Any certificate, without checking it. Anyone on the network can then impersonate the server, so
  only use it for testing.
  -/
  | insecureSkipVerify

/--
What a client trusts and presents.

In `Trust.system` and `Trust.only`, each entry may hold several certificates, and other PEM blocks,
such as keys, are ignored. Any listed certificate can end a chain, not only a root, so an
intermediate CA can be trusted on its own.
-/
structure Config where
  /--
  Which server certificates to accept.
  -/
  trust : Trust := .system
  /--
  The certificate and key to present when a server asks for one (mutual TLS).
  -/
  credentials : Option Credentials := none
  /--
  The lowest TLS version to accept.
  -/
  minVersion : Version := .tls12
  /--
  The highest TLS version to offer.
  -/
  maxVersion : Version := .tls13

@[extern "lean_ssl_ctx_mk_client"]
private opaque mkImpl (trust : @& Trust) (ca : @& Array LoadedPEM) (env : @& Option (Array LoadedPEM))
    (cert key : @& Option LoadedPEM) (minVersion maxVersion : Version) : IO Context.Client

@[extern "lean_ssl_env_ignored"]
private opaque envIgnored : BaseIO Bool

/--
The files `SSL_CERT_FILE` and `SSL_CERT_DIR` name, or `none` if neither is set. Files that can't be
read are skipped, as are the entries of a directory that can't be listed.
-/
private def envAnchors : IO (Option (Array LoadedPEM)) := do
  if ← envIgnored then
    return none

  let nonEmpty (v : Option String) := v.filter (!·.isEmpty)
  let file := nonEmpty (← IO.getEnv "SSL_CERT_FILE")
  let dirs := nonEmpty (← IO.getEnv "SSL_CERT_DIR")

  if file.isNone && dirs.isNone then
    return none

  let mut paths : Array System.FilePath := file.toArray.map (⟨·⟩)
  for dir in System.SearchPath.parse (dirs.getD "") do
    if dir.toString.isEmpty then
      continue
    if let .ok entries ← (System.FilePath.readDir dir).toBaseIO then
      paths := paths ++ entries.map (·.path)

  let mut loaded := #[]
  for path in paths do
    if let .ok bytes ← (IO.FS.readBinFile path).toBaseIO then
      loaded := loaded.push { bytes, path? := some path }
  return some loaded

/--
Creates a client context.

The context only decides which certificates are trusted. It does not check that a certificate
belongs to the server being contacted: the connection does that, given the server's name.
-/
def mk (cfg : Config := {}) : IO Context.Client := do
  let (ca, env) ← match cfg.trust with
    | .system extra => pure (← extra.mapM PEM.load, ← envAnchors)
    | .only ca => pure (← ca.mapM PEM.load, none)
    | .insecureSkipVerify => pure (#[], none)
  let cert ← cfg.credentials.mapM (·.cert.load)
  let key ← cfg.credentials.mapM (·.key.load)
  mkImpl cfg.trust ca env cert key cfg.minVersion cfg.maxVersion

end Client
end Context
end Std.Internal.SSL

end
