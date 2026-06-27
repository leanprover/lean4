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
Creates a new server-side TLS context. The server presents its certificate but does not
authenticate the client (no mutual TLS).
-/
@[extern "lean_ssl_ctx_mk_server"]
opaque mk : IO Context.Server

/--
Loads a PEM certificate and private key into a server context.
-/
@[extern "lean_ssl_ctx_configure_server"]
opaque configure (ctx : @& Context.Server) (certFile : @& String) (keyFile : @& String) : IO Unit

end Server

namespace Client

/--
Creates a new client-side TLS context.

With `defaultVerify := true` (the default) the context trusts the platform's system root store and
verifies the peer certificate, so connections to public HTTPS servers work without further
configuration. A server whose certificate chains only to a private or unknown CA then fails to verify
unless that CA is added with `configure` or `configureFromPEM`.

With `defaultVerify := false` the context performs no peer verification until a later `configure`
call enables it.
-/
@[extern "lean_ssl_ctx_mk_client"]
opaque mk (defaultVerify : Bool := true) : IO Context.Client

/--
Configures CA trust anchors and peer verification for a client context.

Trust-anchor semantics:
- With `verifyPeer := true` the client always trusts the platform default trust anchors (the system
  root store). A non-empty `caFile` is trusted *in addition* to those system anchors, so public
  servers keep working while a private or self-signed CA also becomes trusted.
- An empty `caFile` with `verifyPeer := true` uses just the platform default trust anchors.
- `verifyPeer := false` disables peer verification entirely (the CA file is not parsed).
-/
@[extern "lean_ssl_ctx_configure_client"]
opaque configure (ctx : @& Context.Client) (caFile : @& String) (verifyPeer : Bool) : IO Unit

/--
Configures CA trust anchors from an in-memory PEM string instead of a file path. Accepts one or more
PEM-encoded certificates (same format as a CA bundle file).

Trust-anchor semantics match `configure`:
- With `verifyPeer := true` the client always trusts the platform default trust anchors; a non-empty
  `caPEM` is trusted *in addition* to them.
- An empty `caPEM` with `verifyPeer := true` uses just the platform default trust anchors.
- `verifyPeer := false` disables peer verification entirely (the PEM is not parsed).

Use this when the CA certificate is embedded in the binary rather than on disk.
-/
@[extern "lean_ssl_ctx_configure_client_from_pem"]
opaque configureFromPEM (ctx : @& Context.Client) (caPEM : @& String) (verifyPeer : Bool) : IO Unit

end Client
end Context
end Std.Internal.SSL

end
