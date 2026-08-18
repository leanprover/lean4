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
to be empty is decrypted and trusted there, where the same bytes in `caFile` would be rejected.
-/

public section

namespace Std.Internal.SSL

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
Creates a server-side TLS context, loading the PEM certificate chain and private key from the given
files. The server presents its certificate but does not authenticate the client (no mutual TLS).

`certFile` holds the leaf certificate followed by any intermediates; the whole chain is sent so
clients can build a path to a trusted root. `keyFile` must be an unencrypted key matching that leaf.
-/
@[extern "lean_ssl_ctx_mk_server"]
opaque mk (certFile : @& String) (keyFile : @& String) : IO Context.Server

end Server

namespace Client

/-
A default value on a borrowed parameter wraps its type in `optParam`, which hides the `@&` marker
from the compiler: that parameter is then treated as owned and every argument leaks. So the extern
takes `caFile` explicitly and the public wrapper below carries the default. Only the parameter
carrying the default is affected, which is why `mkFromPEM` needs no such wrapper.
-/
@[extern "lean_ssl_ctx_mk_client"]
private opaque mkImpl (caFile : @& String) (verifyPeer : Bool) : IO Context.Client

/--
Creates a client-side TLS context, reading CA trust anchors from a PEM bundle file.

Trust-anchor semantics:
- With `verifyPeer := true` (the default) the client trusts the platform default trust anchors (the
  system root store) and verifies the peer certificate, so connections to public HTTPS servers work
  out of the box. A non-empty `caFile` is trusted *in addition* to those system anchors, so public
  servers keep working while a private CA also becomes trusted. That CA has to be self-signed: a
  chain is only accepted once it reaches a self-signed certificate, so trusting an intermediate
  alone loads without complaint and then fails every handshake. There is no way to trust `caFile`
  alone, so this cannot be used to pin against a single CA.
- An empty `caFile` with `verifyPeer := true` uses just the platform default trust anchors. Which
  anchors those are is platform-specific: the Keychain on macOS, the `ROOT` store on Windows,
  OpenSSL's configured paths elsewhere. `SSL_CERT_FILE` and `SSL_CERT_DIR` are honoured on every
  platform, and are consulted afresh for every context. On macOS the Keychain is read once per
  process, since doing so costs around a tenth of a second, so a root added to it after the first
  context is built is not picked up until the process restarts. The per-certificate trust settings
  decide, so a root added locally (as `mkcert` and `security add-trusted-cert` do) is trusted and
  one explicitly denied is not; a
  setting that applies only to a named host, key usage, or application grants no trust, since an
  anchor cannot carry that restriction. OpenSSL's own bundle is not merged on top of the Keychain,
  as it would reinstate the roots those settings turned away; it is read only when the Keychain
  yields no anchor at all. `SSL_CERT_FILE` and `SSL_CERT_DIR` name locations of their own, which are
  read in addition to the Keychain and do not drag OpenSSL's bundle in with them.
- `verifyPeer := false` disables peer verification entirely and the CA file is not parsed. This
  cannot be undone: a context built this way can never be made to verify.

`caFile` must be a path without embedded NUL bytes, which is checked before `verifyPeer` is
consulted. Where the file is read, private key and CRL entries are ignored — no revocation checking
is performed — and a file yielding no certificate at all is rejected.

Verifying the peer proves the certificate chains to a trusted anchor; it does **not** prove the
certificate belongs to the host being connected to. Binding a hostname is the session layer's job.
-/
@[inline] def mk (caFile : String := "") (verifyPeer : Bool := true) : IO Context.Client :=
  mkImpl caFile verifyPeer

/--
Creates a client-side TLS context with CA trust anchors from an in-memory PEM string instead of a
file path. Accepts one or more PEM-encoded certificates (same format as a CA bundle file); private
key and CRL entries are ignored, and a string yielding no certificates at all is rejected.

Trust-anchor semantics match `mk`, including that the platform anchors cannot be excluded and that
hostname verification is left to the session layer:
- With `verifyPeer := true` the client always trusts the platform default trust anchors; a non-empty
  `caPEM` is trusted *in addition* to them.
- An empty `caPEM` with `verifyPeer := true` uses just the platform default trust anchors.
- `verifyPeer := false` disables peer verification entirely (the PEM is not parsed).

Unlike `mk`, which takes a path and so rejects embedded NUL bytes, this reads `caPEM` as bytes with
an explicit length, so a NUL does not truncate it. It is still an ordinary junk byte to the PEM
parser, and where it lands decides what happens. A block is recognised only when its line begins with
`-----BEGIN ` and ends with `-----`, so a NUL breaking either of those fixed parts leaves a line that
no longer opens a block and that certificate is dropped without a word. A NUL that leaves the block
open but spoils it — in the type name, in the base64 body, or anywhere in the `-----END` line —
rejects the whole string, valid certificates alongside it included. Outside any block it is harmless.

Use this when the CA certificate is embedded in the binary rather than on disk.
-/
@[extern "lean_ssl_ctx_mk_client_from_pem"]
opaque mkFromPEM (caPEM : @& String) (verifyPeer : Bool := true) : IO Context.Client

end Client
end Context
end Std.Internal.SSL

end
