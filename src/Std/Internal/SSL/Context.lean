/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module
prelude
public import Init.System.IO

/-!
TLS contexts for servers and clients: the certificate and key, the peer verification mode, and the
protocol options shared by every session created from a context.

Every context requires TLS 1.2 or later, allows only ECDHE with AES-GCM or ChaCha20-Poly1305 (and
the matching TLS 1.3 suites), runs at OpenSSL security level 2, and disables session tickets,
resumption, compression and renegotiation. A toolchain linking the system's OpenSSL also reads its
configuration, which can tighten these settings but not loosen them; a context whose configuration
leaves no allowed suite for a TLS version it permits is refused.

Encrypted certificates and keys are refused rather than prompted for. Material reached through
`SSL_CERT_FILE` or `SSL_CERT_DIR` is the exception: OpenSSL reads it with an empty passphrase.
-/

public section

namespace Std.Internal.SSL

/--
PEM-encoded material, given either as the path of a file holding it or as its contents. A path
containing a NUL byte is rejected; in `PEM.text` a NUL is ordinary input to the PEM parser.
-/
inductive PEM where

  /--
  Read the PEM from the file at `path`.
  -/
  | file (path : System.FilePath)

  /--
  Take `contents` as the PEM bytes themselves.
  -/
  | text (contents : String)

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
The credentials a server presents.
-/
structure Config where
  /--
  The leaf certificate followed by any intermediates. The whole chain is sent, so clients can build
  a path to a trusted root.
  -/
  cert : PEM
  /-- An unencrypted private key matching the leaf in `cert`. -/
  key : PEM

@[extern "lean_ssl_ctx_mk_server"]
private opaque mkImpl (cert : @& PEM) (key : @& PEM) : IO Context.Server

/--
Creates a server-side TLS context from a certificate chain and private key. The server does not
authenticate clients (no mutual TLS).

Certificates are not checked against the clock, so an expired one loads here and the peer rejects it
during the handshake. A key that does not match the leaf certificate is rejected, as is an encrypted
key.
-/
def mk (cfg : Config) : IO Context.Server :=
  mkImpl cfg.cert cfg.key

end Server

namespace Client

/--
Which anchors a client trusts, and whether it checks the peer against them at all.
-/
structure Config where
  /--
  Trust anchors supplied by the caller, trusted alongside the platform anchors or, with
  `trustSystemRoots := false`, instead of them.

  Private keys and CRLs in the material are ignored; material holding no certificate is rejected.
  A `TRUSTED CERTIFICATE` block rejecting a certificate is only certain to take effect with
  `trustSystemRoots := false`, since the platform's own verdict on that certificate can take
  precedence.
  -/
  ca : Option PEM := none
  /--
  Whether to verify that the peer certificate chains to a trusted anchor. With `false` neither `ca`
  nor the platform anchors are consulted, and the context can never be made to verify.
  -/
  verifyPeer : Bool := true
  /--
  Whether the platform's trust anchors are trusted, so that public HTTPS servers work out of the box.
  With `false` only `ca` is trusted, and neither the platform nor the environment is consulted.

  * macOS: a chain that neither `ca` nor the environment's anchors establish goes to the system's
    trust evaluation during the handshake. It applies the Keychain's current trust settings and
    Apple's TLS requirements, such as Certificate Transparency, CA distrust dates, pinned Apple
    hosts, and at most 825 days of validity even under a locally trusted root. OpenSSL then checks
    the chain it settles on again, so hostname rules are at least as strict as on other platforms.
    Missing intermediates are never fetched: the server, `ca` or the environment has to supply them.
  * Windows: the `ROOT` certificate store, which needs OpenSSL 3.2 or later. Windows adds most roots
    to it on demand, the first time its own chain engine needs one, so a public root no Windows
    program on the machine has used yet is missing; supply it through `ca` or `SSL_CERT_FILE`. The
    `Disallowed` store and per-certificate properties are not consulted.
  * Elsewhere: the usual system bundle locations.

  A toolchain linking the system's OpenSSL also reads that library's compiled-in certificate paths
  (on Windows only when the `ROOT` store is unavailable); a standalone toolchain never does.

  `SSL_CERT_FILE` and `SSL_CERT_DIR` are read for every verifying context and add to the platform
  anchors, except in a set-user-ID or set-group-ID process. On macOS a chain that they or `ca`
  establish is accepted without the system evaluation. A variable naming an unreadable file is only
  reported when no other anchor was found.

  Lean performs no revocation checking of its own.
  -/
  trustSystemRoots : Bool := true
  /--
  Whether a certificate in the trust store may anchor a chain without being self-signed.

  With `false`, the default, a chain must reach a self-signed certificate or one a `TRUSTED
  CERTIFICATE` block trusts for TLS servers. A `ca` of only intermediates with
  `trustSystemRoots := false` could then never verify anything, and is refused. With `true` any
  certificate in the store anchors a chain, as pinning an intermediate requires. On macOS a Keychain
  trust setting on an intermediate or leaf makes it an anchor regardless of this flag.
  -/
  allowPartialChain : Bool := false

@[extern "lean_ssl_ctx_mk_client"]
private opaque mkImpl (ca : @& Option PEM) (verifyPeer : Bool) (trustSystemRoots : Bool)
    (allowPartialChain : Bool) : IO Context.Client

/--
Creates a client-side TLS context trusting the anchors named by `cfg`.

To pin a specific CA, use `{ ca := some ca, trustSystemRoots := false }`: certificates from any other
authority, public roots included, are then rejected. `ca` must then supply an anchor, which is
checked here rather than at every handshake. The same holds when `trustSystemRoots` is set but the
platform supplies no anchors; without `ca` that case is refused.

Verification proves the certificate chains to a trusted anchor, **not** that it belongs to the host
being connected to. Binding a hostname is the session layer's job.
-/
def mk (cfg : Config := {}) : IO Context.Client :=
  mkImpl cfg.ca cfg.verifyPeer cfg.trustSystemRoots cfg.allowPartialChain

end Client
end Context
end Std.Internal.SSL

end
