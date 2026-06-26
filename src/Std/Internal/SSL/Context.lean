/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module
prelude
public import Init.System.Promise

/-!
OpenSSL context types for server and client TLS sessions. Contexts configure the TLS method,
certificate/key, peer-verification mode, and protocol options shared across all sessions created
from the same context.

For every context session tickets and TLS compression are disabled and TLS 1.2 is the minimum
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
Creates a new server-side TLS context. Only the server certificate is authenticated; set
`defaultVerify := true` if you want the server context to start with peer verification enabled.
-/
@[extern "lean_ssl_ctx_mk_server"]
opaque mk (defaultVerify : Bool := false) : IO Context.Server

/--
Loads a PEM certificate and private key into a server context.
-/
@[extern "lean_ssl_ctx_configure_server"]
opaque configure (ctx : @& Context.Server) (certFile : @& String) (keyFile : @& String) : IO Unit

end Server

namespace Client

/--
Creates a new client-side TLS context. Connecting to a server with a self-signed or unknown CA
certificate will fail unless `configure` is called first with that CA file.
-/
@[extern "lean_ssl_ctx_mk_client"]
opaque mk (defaultVerify : Bool := true) : IO Context.Client

/--
Configures CA trust anchors and peer verification for a client context.

Trust-anchor semantics:
- A non-empty `caFile` pins trust to exactly those CA certificates; the platform default trust
  anchors are **not** added.
- An empty `caFile` with `verifyPeer := true` uses the platform default trust anchors.
- `verifyPeer := false` disables peer verification entirely.
-/
@[extern "lean_ssl_ctx_configure_client"]
opaque configure (ctx : @& Context.Client) (caFile : @& String) (verifyPeer : Bool) : IO Unit

/--
Configures CA trust anchors from an in-memory PEM string instead of a file path. Accepts one or more
PEM-encoded certificates (same format as a CA bundle file).

Trust-anchor semantics match `configure`:
- A non-empty `caPEM` pins trust to exactly those CA certificates; the platform default trust
  anchors are **not** added.
- An empty `caPEM` with `verifyPeer := true` uses the platform default trust anchors.
- `verifyPeer := false` disables peer verification entirely (the PEM is not parsed).

Use this when the CA certificate is embedded in the binary rather than on disk.
-/
@[extern "lean_ssl_ctx_configure_client_from_pem"]
opaque configureFromPEM (ctx : @& Context.Client) (caPEM : @& String) (verifyPeer : Bool) : IO Unit

end Client
end Context
end Std.Internal.SSL

end
