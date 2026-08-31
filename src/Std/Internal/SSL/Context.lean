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
TLS 1.2 is the minimum version. A server built here therefore offers no session resumption; a client
does not resume either, since resuming additionally requires selecting a session per connection,
which the session layer never does.

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

  Private key and CRL entries in the material are ignored, so a bundle may hold them; no revocation
  checking is performed. Material yielding no certificate at all is rejected.
  -/
  ca : Option PEM := none
  /--
  Whether to verify that the peer certificate chains to a trusted anchor. `false` disables
  verification entirely, and neither `ca` nor the platform anchors are then consulted. This cannot
  be undone: a context built this way can never be made to verify.
  -/
  verifyPeer : Bool := true
  /--
  Whether the platform default trust anchors are trusted.

  With `true`, connections to public HTTPS servers work out of the box. Which anchors those are is
  platform-specific: the Keychain on macOS, the `ROOT` store on Windows, OpenSSL's configured paths
  elsewhere. `SSL_CERT_FILE` and `SSL_CERT_DIR` are honoured on every platform, and are consulted
  afresh for every context. On macOS the Keychain is read once per process, since doing so costs
  around a tenth of a second, so a root added to it after the first context is built is not picked
  up until the process restarts. The per-certificate trust settings decide, so a root added locally
  (as `mkcert` and `security add-trusted-cert` do) is trusted and one explicitly denied is not; a
  setting that applies only to a named host, key usage, or application grants no trust, since an
  anchor cannot carry that restriction. OpenSSL's own bundle is not merged on top of the Keychain,
  as it would reinstate the roots those settings turned away; it is read only when the Keychain
  yields no anchor at all. `SSL_CERT_FILE` and `SSL_CERT_DIR` name locations of their own, which are
  read in addition to the Keychain and do not drag OpenSSL's bundle in with them.

  With `false` none of that is consulted, environment variables included, and only `ca` is trusted.
  -/
  trustSystemRoots : Bool := true

@[extern "lean_ssl_ctx_mk_client"]
private opaque mkImpl (ca : @& String) (caIsFile : Bool) (hasCA : Bool) (verifyPeer : Bool)
    (trustSystemRoots : Bool) : IO Context.Client

/--
Creates a client-side TLS context trusting the anchors named by `cfg`.

Pinning against a specific CA is `{ ca := some ca, trustSystemRoots := false }`: a certificate
issued by any other authority, public roots included, is then rejected. `ca` must supply at least
one certificate in that case, since a verifying context with no anchor at all could never complete a
handshake; that combination is refused here rather than at connection time.

A trusted CA has to be self-signed, whichever way it is supplied: a chain is only accepted once it
reaches a self-signed certificate, so trusting an intermediate alone loads without complaint and
then fails every handshake.

Verifying the peer proves the certificate chains to a trusted anchor; it does **not** prove the
certificate belongs to the host being connected to. Binding a hostname is the session layer's job.
-/
def mk (cfg : Config := {}) : IO Context.Client :=
  match cfg.ca with
  | none => mkImpl "" false false cfg.verifyPeer cfg.trustSystemRoots
  | some ca => mkImpl ca.bytes ca.isFile true cfg.verifyPeer cfg.trustSystemRoots

end Client
end Context
end Std.Internal.SSL

end
