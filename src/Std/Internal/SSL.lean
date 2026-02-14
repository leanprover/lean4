/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init.System.Promise

public section

namespace Std
namespace Internal
namespace SSL

private opaque SessionImpl : NonemptyType.{0}

/--
Represents an OpenSSL session backed by memory BIOs.
-/
def Session : Type := SessionImpl.type

instance : Nonempty Session := by exact SessionImpl.property

/--
Configures the shared server context with a certificate and key in PEM format.
-/
@[extern "lean_uv_ssl_configure_server_ctx"]
opaque configureServerContext (certFile : @& String) (keyFile : @& String) : IO Unit

/--
Configures the shared client context.
`caFile` may be empty to keep default trust configuration.
-/
@[extern "lean_uv_ssl_configure_client_ctx"]
opaque configureClientContext (caFile : @& String) (verifyPeer : Bool) : IO Unit

namespace Session

/--
Creates a new SSL session. Set `isServer := true` for server-side handshakes.
-/
@[extern "lean_uv_ssl_mk"]
opaque mk (isServer : Bool) : IO Session

/--
Creates a server-side SSL session.
-/
@[extern "lean_uv_ssl_mk_server"]
opaque mkServer : IO Session

/--
Creates a client-side SSL session.
-/
@[extern "lean_uv_ssl_mk_client"]
opaque mkClient : IO Session

/--
Sets SNI host name for client-side handshakes.
-/
@[extern "lean_uv_ssl_set_server_name"]
opaque setServerName (ssl : @& Session) (host : @& String) : IO Unit

/--
Gets the X.509 verify result code after handshake.
-/
@[extern "lean_uv_ssl_verify_result"]
opaque verifyResult (ssl : @& Session) : IO UInt64

/--
Runs one handshake step. Returns true when handshake is complete.
-/
@[extern "lean_uv_ssl_handshake"]
opaque handshake (ssl : @& Session) : IO Bool

/--
Attempts to write plaintext application data into SSL.
Returns true when accepted, false when OpenSSL needs more I/O first.
-/
@[extern "lean_uv_ssl_write"]
opaque write (ssl : @& Session) (data : @& ByteArray) : IO Bool

/--
Attempts to read decrypted plaintext data. Returns none when OpenSSL needs more I/O.
-/
@[extern "lean_uv_ssl_read"]
opaque read? (ssl : @& Session) (maxBytes : UInt64) : IO (Option ByteArray)

/--
Feeds encrypted TLS bytes into the SSL input BIO.
-/
@[extern "lean_uv_ssl_feed_encrypted"]
opaque feedEncrypted (ssl : @& Session) (data : @& ByteArray) : IO UInt64

/--
Drains encrypted TLS bytes from the SSL output BIO.
-/
@[extern "lean_uv_ssl_drain_encrypted"]
opaque drainEncrypted (ssl : @& Session) : IO ByteArray

/--
Returns the amount of encrypted TLS bytes currently pending in the output BIO.
-/
@[extern "lean_uv_ssl_pending_encrypted"]
opaque pendingEncrypted (ssl : @& Session) : IO UInt64

/--
Returns the amount of decrypted plaintext bytes currently buffered inside the SSL object.
-/
@[extern "lean_uv_ssl_pending_plaintext"]
opaque pendingPlaintext (ssl : @& Session) : IO UInt64

end Session
end SSL
end Internal
end Std
