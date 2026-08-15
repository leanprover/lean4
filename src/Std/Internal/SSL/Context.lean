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
TLS 1.2 is the minimum version. Session resumption is therefore not supported.

A context settles who is trusted, not who is being talked to: nothing here checks that a peer
certificate matches the host it came from. That check belongs to the session layer, which binds a
hostname per connection.

Encrypted PEM material is rejected rather than prompted for, so no constructor can block on a
terminal.
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
  servers keep working while a private or self-signed CA also becomes trusted. There is no way to
  trust `caFile` alone, so this cannot be used to pin against a single CA.
- An empty `caFile` with `verifyPeer := true` uses just the platform default trust anchors. Which
  anchors those are is platform-specific: the Keychain system roots on macOS, the `ROOT` store on
  Windows, OpenSSL's configured paths elsewhere. `SSL_CERT_FILE` and `SSL_CERT_DIR` are honoured on
  every platform, but user-added or explicitly distrusted keychain entries are not consulted.
- `verifyPeer := false` disables peer verification entirely and the CA file is not parsed. This
  cannot be undone: a context built this way can never be made to verify.

`caFile` must be a path without embedded NUL bytes, which is checked before `verifyPeer` is
consulted. A file containing no certificates is rejected.

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
an explicit length: a NUL is ordinary data and the certificates around it are still parsed.

Use this when the CA certificate is embedded in the binary rather than on disk.
-/
@[extern "lean_ssl_ctx_mk_client_from_pem"]
opaque mkFromPEM (caPEM : @& String) (verifyPeer : Bool := true) : IO Context.Client

end Client
end Context
end Std.Internal.SSL

end
