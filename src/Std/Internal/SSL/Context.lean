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

For every context, session tickets and TLS compression are disabled and TLS 1.2 is the minimum
version. Session resumption is therefore not supported.
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
-/
@[extern "lean_ssl_ctx_mk_server"]
opaque mk (certFile : @& String) (keyFile : @& String) : IO Context.Server

end Server

namespace Client

/-
A default value on a borrowed parameter wraps its type in `optParam`, which hides the `@&` marker
from the compiler: the parameter is then treated as owned and every argument leaks. So the extern
takes `caFile` explicitly and the public wrapper below carries the default.
-/
@[extern "lean_ssl_ctx_mk_client"]
private opaque mkImpl (caFile : @& String) (verifyPeer : Bool) : IO Context.Client

/--
Creates a client-side TLS context.

Trust-anchor semantics:
- With `verifyPeer := true` (the default) the client trusts the platform default trust anchors (the
  system root store) and verifies the peer certificate, so connections to public HTTPS servers work
  out of the box. A non-empty `caFile` is trusted *in addition* to those system anchors, so public
  servers keep working while a private or self-signed CA also becomes trusted.
- An empty `caFile` with `verifyPeer := true` uses just the platform default trust anchors.
- `verifyPeer := false` disables peer verification entirely (the CA file is not parsed).
-/
@[inline] def mk (caFile : String := "") (verifyPeer : Bool := true) : IO Context.Client :=
  mkImpl caFile verifyPeer

/--
Creates a client-side TLS context with CA trust anchors from an in-memory PEM string instead of a
file path. Accepts one or more PEM-encoded certificates (same format as a CA bundle file).

Trust-anchor semantics match `mk`:
- With `verifyPeer := true` the client always trusts the platform default trust anchors; a non-empty
  `caPEM` is trusted *in addition* to them.
- An empty `caPEM` with `verifyPeer := true` uses just the platform default trust anchors.
- `verifyPeer := false` disables peer verification entirely (the PEM is not parsed).

Use this when the CA certificate is embedded in the binary rather than on disk.
-/
@[extern "lean_ssl_ctx_mk_client_from_pem"]
opaque mkFromPEM (caPEM : @& String) (verifyPeer : Bool := true) : IO Context.Client

end Client
end Context
end Std.Internal.SSL

end
