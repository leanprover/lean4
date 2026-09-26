/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module
prelude
public import Init.System.IO

/-!
TLS contexts. A context holds what every connection made from it shares: for a server, the
certificate and key it presents; for a client, the certificates it trusts. Create one context and
reuse it for many connections. It cannot be changed after creation and can be shared between threads.

```lean
-- A client that trusts the system's root certificates.
let client ← Context.Client.mk

-- A client that trusts only your own CA.
let pinned ← Context.Client.mk { ca := #[.file "ca.pem"], trustSystemRoots := false }

-- A server.
let server ← Context.Server.mk { cert := .file "cert.pem", key := .file "key.pem" }
```

Files are read when the context is created, so a renewed certificate needs a new context.

## Security settings

Every context requires TLS 1.2 or later. TLS 1.2 connections only use ECDHE key exchange with
AES-GCM or ChaCha20-Poly1305; TLS 1.3 uses its three standard cipher suites. RSA keys must be at
least 2048 bits. Session resumption, compression and
renegotiation are off, and encrypted keys are refused rather than prompting for a passphrase.

When Lean uses the system's OpenSSL, that library's configuration can make these settings stricter
but not looser. If it leaves no usable cipher suite, creating a context fails.

## Errors

* `invalidArgument`: the configuration or the PEM material can't be used. The error names the file
  when the material came from one.
* `noSuchThing`: the system has no root certificates to trust, and `ca` is empty.
* `unsupportedOperation`: the system's OpenSSL configuration leaves no cipher suite these settings
  allow, or this build of Lean has no TLS support.
* `userError`: OpenSSL failed for some other reason.
* Errors from reading a file are those of `IO.FS.readBinFile`.

## Platform notes

The system's root certificates come from:

* macOS: the Keychain. A chain that OpenSSL can't verify on its own goes to the system's trust
  evaluation, which also applies Apple's rules, such as Certificate Transparency and limits on
  certificate lifetime. Missing intermediate certificates are never downloaded.
* Windows: the `ROOT` certificate store, which needs OpenSSL 3.2 or later. Windows only adds a root
  to this store the first time something on the machine needs it, so a root may be missing; pass it
  in `ca`. The `Disallowed` store is not checked.
* Linux and others: the distribution's certificate bundle and certificate directories.

`SSL_CERT_FILE` and `SSL_CERT_DIR` add more certificates to trust, except in set-user-ID and
set-group-ID programs. Except on macOS, a Lean build that uses the system's OpenSSL also reads
OpenSSL's default certificate locations. None of this is read with `trustSystemRoots := false`.

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
What a server presents to clients.
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

@[extern "lean_ssl_ctx_mk_server"]
private opaque mkImpl (cert : @& LoadedPEM) (key : @& LoadedPEM) : IO Context.Server

/--
Creates a server context. Fails if the key doesn't match the certificate, or if either can't be read.

Clients are not asked for a certificate (no mutual TLS). An expired certificate is accepted here and
rejected by clients during the handshake.
-/
def mk (cfg : Config) : IO Context.Server := do
  mkImpl (← cfg.cert.load) (← cfg.key.load)

end Server

namespace Client

/--
Which certificates a client trusts.
-/
structure Config where
  /--
  CA certificates to trust in addition to, or with `trustSystemRoots := false` instead of, the
  system's. An entry may hold several certificates; other PEM blocks, such as keys, are ignored.
  -/
  ca : Array PEM := #[]
  /--
  Whether to check the server's certificate at all. With `false` any certificate is accepted, so
  anyone on the network can impersonate the server. Only use it for testing.
  -/
  verifyPeer : Bool := true
  /--
  Whether to trust the system's root certificates. See the platform notes in the module
  documentation for where they come from.
  -/
  trustSystemRoots : Bool := true
  /--
  Whether a trusted certificate may end a chain without being a root. This is what trusting an
  intermediate CA on its own requires.
  -/
  allowPartialChain : Bool := false

@[extern "lean_ssl_ctx_mk_client"]
private opaque mkImpl (ca : @& Array LoadedPEM) (verifyPeer : Bool) (trustSystemRoots : Bool)
    (allowPartialChain : Bool) : IO Context.Client

/--
Creates a client context.

The context only decides which certificates are trusted. It does not check that a certificate
belongs to the server being contacted: the connection does that, given the server's name.

When `ca` is the only source of trust, it must hold a root certificate (or, with
`allowPartialChain`, any certificate). This is checked here, not at every connection.
-/
def mk (cfg : Config := {}) : IO Context.Client := do
  if cfg.verifyPeer && !cfg.trustSystemRoots && cfg.ca.isEmpty then
    -- 22 is `EINVAL`, the code the runtime gives unusable material.
    throw <| .invalidArgument none 22
      "no trust anchors: `trustSystemRoots := false` needs at least one certificate in `ca`"

  -- Without verification the CA material is not even read.
  let ca ← if cfg.verifyPeer then cfg.ca.mapM PEM.load else pure #[]
  mkImpl ca cfg.verifyPeer cfg.trustSystemRoots cfg.allowPartialChain

end Client
end Context
end Std.Internal.SSL

end
