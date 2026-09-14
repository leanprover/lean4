/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module
prelude
public import Init.System.IO

/-!
OpenSSL context types for server and client TLS sessions. Contexts configure the TLS method,
certificate/key, peer-verification mode, and protocol options shared across all sessions created
from the same context.

For every context, session tickets and TLS compression are disabled, renegotiation is refused, and
TLS 1.2 is the minimum version. TLS 1.2 is limited to suites with forward secrecy and authenticated
encryption (ECDHE with AES-GCM or ChaCha20-Poly1305), and keys and signatures to OpenSSL's security
level 2. OpenSSL's configuration file is never read, so none of this depends on the machine. A server
built here offers no session resumption; a client does not resume either, since resuming additionally
requires selecting a session per connection, which the session layer never does.

A context settles who is trusted, not who is being talked to: nothing here checks that a peer
certificate matches the host it came from. That check belongs to the session layer, which binds a
hostname per connection.

The certificate, key and CA material passed to these constructors is refused outright when it is
encrypted, rather than prompted for, so no constructor can block on a terminal asking for a
passphrase. Material reached through `SSL_CERT_FILE` or `SSL_CERT_DIR` is read by OpenSSL with an
empty passphrase instead: it cannot prompt either, but an encrypted block whose passphrase happens
to be empty is decrypted and trusted there, where the same bytes in a `PEM.file` would be rejected.
-/

public section

namespace Std.Internal.SSL

/--
PEM-encoded material, named either by the path of a file holding it or by its bytes directly.

The two differ in how a NUL byte is treated. A path is passed to the OS as a C string, so an
embedded NUL is rejected outright; `PEM.text` is read with an explicit length, so a NUL is ordinary
input the PEM parser then has to make sense of.
-/
inductive PEM where

  /--
  Read the PEM from the file at `path`.
  -/
  | file (path : String)

  /--
  Take `contents` as the PEM bytes themselves.
  -/
  | text (contents : String)

namespace PEM

@[inline] private def bytes : PEM → String
  | .file path => path
  | .text contents => contents

@[inline] private def isFile : PEM → Bool
  | .file _ => true
  | .text _ => false

end PEM

private opaque ContextServerImpl : NonemptyType.{0}

/--
Server-side TLS context (`SSL_CTX` configured with `TLS_server_method`).
-/
def Context.Server : Type := ContextServerImpl.type

instance : Nonempty Context.Server := ContextServerImpl.property

private opaque ContextClientImpl : NonemptyType.{0}

/--
Client-side TLS context (`SSL_CTX` configured with `TLS_client_method`).
-/
def Context.Client : Type := ContextClientImpl.type

instance : Nonempty Context.Client := ContextClientImpl.property

namespace Context.Server

/--
The credentials a server presents. Both fields are required: a server that cannot prove who it is
has nothing to offer a client.
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
private opaque mkImpl (cert : @& String) (certIsFile : Bool) (key : @& String) (keyIsFile : Bool) :
    IO Context.Server

/--
Creates a server-side TLS context from the given certificate chain and private key. The server
presents its certificate but does not authenticate the client (no mutual TLS).

The certificate is parsed but not validated against the clock: an expired certificate loads here and
is rejected by the peer at handshake time. A key that does not match the leaf certificate is
rejected, as is an encrypted key — decrypting one would mean asking for a passphrase.
-/
def mk (cfg : Config) : IO Context.Server :=
  mkImpl cfg.cert.bytes cfg.cert.isFile cfg.key.bytes cfg.key.isFile

end Server

namespace Client

/--
Which anchors a client trusts, and whether it checks the peer against them at all.
-/
structure Config where
  /--
  Trust anchors supplied by the caller, trusted in addition to the platform anchors or — with
  `trustSystemRoots := false` — instead of them. `none` supplies no anchors of its own.

  Private key and CRL entries in the material are ignored, so a bundle may hold them; Lean performs
  no revocation checking of its own. Material yielding no certificate at all is rejected.
  -/
  ca : Option PEM := none
  /--
  Whether to verify that the peer certificate chains to a trusted anchor. `false` disables
  verification entirely, and neither `ca` nor the platform anchors are then consulted. This cannot
  be undone: a context built this way can never be made to verify.
  -/
  verifyPeer : Bool := true
  /--
  Whether the platform's trust anchors are trusted, so that connections to public HTTPS servers work
  out of the box. With `false` only `ca` is trusted, and neither the platform nor the environment is
  consulted.

  Which anchors those are depends on the platform:
  * On macOS, a chain that neither `ca` nor the environment's anchors establish is handed to the
    system's trust evaluation during the handshake. It applies the Keychain's trust settings as they
    stand at that moment (a root added as `mkcert` and `security add-trusted-cert` do is trusted, one
    explicitly denied is not) and Apple's requirements for TLS certificates, such as Certificate
    Transparency, CA distrust dates, and a validity of at most 825 days even under a locally trusted
    root. The chain it settles on is then checked again by OpenSSL, so the hostname rules are those
    of every other platform. The evaluation never fetches a missing intermediate over the network, so
    the server has to send its whole chain.
  * On Windows, the `ROOT` certificate store, which needs OpenSSL 3.2 or later; the `Disallowed`
    store and per-certificate properties are not consulted. OpenSSL's compiled-in certificate paths
    are read only when the `ROOT` store is unavailable, since they name directories on the machine
    the build ran on.
  * Elsewhere, OpenSSL's compiled-in certificate paths, and where those hold nothing — as for a
    binary built against a relocated OpenSSL — the usual system bundle locations.

  `SSL_CERT_FILE` and `SSL_CERT_DIR` are read afresh for every context and add their anchors to the
  platform's, except in a set-user-ID or set-group-ID process, which ignores them. On macOS a chain
  that `ca` or one of those anchors establishes is accepted on OpenSSL's verdict alone, without the
  system evaluation. A variable naming a missing or unreadable file is reported only when no anchor
  was found anywhere else.

  Lean performs no revocation checking of its own.
  -/
  trustSystemRoots : Bool := true
  /--
  Whether a certificate in the trust store may anchor a chain without being self-signed itself.

  With `false`, the default, a chain is accepted only once it reaches a self-signed certificate, or
  one whose `TRUSTED CERTIFICATE` block explicitly trusts it for TLS servers, so an ordinary
  intermediate CA cannot serve as a trust anchor. Supplying nothing but intermediates as `ca`
  while also excluding the platform anchors then describes a context that could never verify
  anything, and is rejected outright rather than left to fail at every handshake. Alongside the
  platform anchors an intermediate is merely redundant, so it passes.

  With `true` any certificate in the store anchors a chain, which is what pinning to an intermediate
  rather than to the root above it requires. On macOS, independently of this flag, a Keychain trust
  setting on an intermediate or leaf makes it an anchor for the system evaluation.
  -/
  allowPartialChain : Bool := false

@[extern "lean_ssl_ctx_mk_client"]
private opaque mkImpl (ca : @& String) (caIsFile : Bool) (hasCA : Bool) (verifyPeer : Bool)
    (trustSystemRoots : Bool) (allowPartialChain : Bool) : IO Context.Client

/--
Creates a client-side TLS context trusting the anchors named by `cfg`.

Pinning against a specific CA is `{ ca := some ca, trustSystemRoots := false }`: a certificate
issued by any other authority, public roots included, is then rejected. `ca` must supply at least
one certificate in that case, since a verifying context with no anchor at all could never complete a
handshake; that combination is refused here rather than at connection time.

A trusted CA has to be self-signed, or explicitly trusted for TLS servers, unless `allowPartialChain`
says otherwise. Pinning to nothing but ordinary intermediates is refused here rather than failing at
every handshake.

Verifying the peer proves the certificate chains to a trusted anchor; it does **not** prove the
certificate belongs to the host being connected to. Binding a hostname is the session layer's job.
-/
def mk (cfg : Config := {}) : IO Context.Client :=
  match cfg.ca with
  | none => mkImpl "" false false cfg.verifyPeer cfg.trustSystemRoots cfg.allowPartialChain
  | some ca =>
    mkImpl ca.bytes ca.isFile true cfg.verifyPeer cfg.trustSystemRoots cfg.allowPartialChain

end Client
end Context
end Std.Internal.SSL

end
