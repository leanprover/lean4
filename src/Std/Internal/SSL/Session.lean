/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module
prelude
public import Std.Internal.SSL.Context

/-!
Low-level OpenSSL session API: memory-BIO–based SSL state machine with explicit encrypted I/O
(`feedEncrypted`, `drainEncrypted`) and plaintext I/O (`write`, `read?`). Use `Std.Async.TCP.SSL`
for the high-level TCP socket layer.
-/

public section

namespace Std.Internal.SSL

private opaque SessionImpl : NonemptyType.{0}

/--
Represents an OpenSSL SSL session. Use `Session.Server.mk` / `Session.Client.mk` to create
role-specific sessions.
-/
def Session : Type := SessionImpl.type

instance : Nonempty Session := SessionImpl.property

/--
Server-side TLS session. Wraps `Session` to prevent mixing server and client roles at the type level.
-/
structure Session.Server where
  private ofSession ::
  toSession : Session

/--
Client-side TLS session. Wraps `Session` to prevent mixing server and client roles at the type level.
-/
structure Session.Client where
  private ofSession ::
  toSession : Session

/--
Indicates what kind of socket I/O OpenSSL needs before the current operation can proceed.
-/
inductive IOWant where

  /--
  OpenSSL needs more encrypted bytes from the socket (`SSL_ERROR_WANT_READ`).
  -/
  | read

  /--
  OpenSSL needs to flush encrypted bytes to the socket (`SSL_ERROR_WANT_WRITE`).
  -/
  | write

/--
Result of a `Session.read?` call.
-/
inductive ReadResult where

  /--
  Plaintext data was successfully decrypted.
  -/
  | data (bytes : ByteArray)

  /--
  OpenSSL needs socket I/O before it can produce plaintext.
  -/
  | wantIO (want : IOWant)

  /--
  The peer closed the TLS session cleanly (`SSL_ERROR_ZERO_RETURN`).
  -/
  | closed

namespace Session.Server

@[extern "lean_ssl_mk_server"]
private opaque mkImpl (ctx : @& Context.Server) : IO Session

/--
Creates a new server-side SSL session from the given context.
-/
def mk (ctx : @& Context.Server) : IO Session.Server :=
  return ⟨← mkImpl ctx⟩

end Server
namespace Client

@[extern "lean_ssl_mk_client"]
private opaque mkImpl (ctx : @& Context.Client) : IO Session

/--
Creates a new client-side SSL session from the given context.
-/
def mk (ctx : @& Context.Client) : IO Session.Client :=
  return ⟨← mkImpl ctx⟩

end Client

/--
Backing primitive for `Session.Client.setServerName`. Kept private so the SNI / hostname-verification
setting can only be applied to a client session, never a server one (see `Session.Client.setServerName`).
-/
@[extern "lean_ssl_set_server_name"]
private opaque setServerNameImpl (ssl : @& Session) (host : @& String) : IO Unit

/--
Gets the X.509 verification result code after the handshake (`0` is `X509_V_OK`).

OpenSSL also returns `X509_V_OK` when the peer presented no certificate at all, so a `0` result
does not by itself prove an authenticated peer; confirm a certificate was received when that matters.
-/
@[extern "lean_ssl_verify_result"]
opaque verifyResult (ssl : @& Session) : IO UInt64

/--
Gets the human-readable X.509 verify result string after handshake.
-/
@[extern "lean_ssl_verify_result_string"]
opaque verifyResultString (ssl : @& Session) : IO String

/--
Runs one handshake step. Returns `none` when the handshake is complete, or `some w` when OpenSSL
needs socket I/O of kind `w` before the handshake can proceed.
-/
@[extern "lean_ssl_handshake"]
opaque handshake (ssl : @& Session) : IO (Option IOWant)

/--
Attempts to write plaintext application data into SSL. Returns `none` when all queued plaintext
(including `data`) has been accepted; encrypted output is then ready to drain with `drainEncrypted`.
Returns `some w` when OpenSSL needs socket I/O of kind `w` before the write can complete; in that
case the data has been queued internally and **must not** be submitted again — call `write` again
with an empty `data` once the I/O is satisfied to keep draining the queue.

Passing an empty `data` does not enqueue anything: it only flushes any previously queued plaintext
and reports whether the queue is now drained (`none`) or still blocked (`some w`).
-/
@[extern "lean_ssl_write"]
opaque write (ssl : @& Session) (data : @& ByteArray) : IO (Option IOWant)

/--
Attempts to read decrypted plaintext data.

At most one TLS record's worth of plaintext (16 KiB, `SSL3_RT_MAX_PLAIN_LENGTH`) is returned per
call, regardless of `maxBytes`; call again to read further data.

When `maxBytes == 0`, performs a non-consuming peek: returns `.data ByteArray.empty` if any
plaintext is available (without consuming it), `.closed` if the peer has sent `close_notify`, or
`.wantIO` if more socket I/O is needed first. This lets a caller test readability without committing
to a read.
-/
@[extern "lean_ssl_read"]
opaque read? (ssl : @& Session) (maxBytes : UInt64) : IO ReadResult

/--
Feeds encrypted TLS bytes into the SSL input BIO and returns the number of bytes written.

The input BIO is an in-memory BIO, which never performs a short write: this consumes all of `data`
(so the result always equals `data.size`) or raises on a fatal BIO error.
-/
@[extern "lean_ssl_feed_encrypted"]
opaque feedEncrypted (ssl : @& Session) (data : @& ByteArray) : IO UInt64

/--
Drains encrypted TLS bytes from the SSL output BIO.
-/
@[extern "lean_ssl_drain_encrypted"]
opaque drainEncrypted (ssl : @& Session) : IO ByteArray

/--
Returns the amount of encrypted TLS bytes currently pending in the output BIO.
-/
@[extern "lean_ssl_pending_encrypted"]
opaque pendingEncrypted (ssl : @& Session) : IO UInt64

/--
Returns the amount of decrypted plaintext bytes currently buffered inside the SSL object.
-/
@[extern "lean_ssl_pending_plaintext"]
opaque pendingPlaintext (ssl : @& Session) : IO UInt64

/--
Returns the negotiated TLS protocol version string, e.g. `"TLSv1.3"` or `"TLSv1.2"`.

Before the handshake completes this returns the highest protocol version the session is configured
to offer rather than a negotiated value, so only treat the result as authoritative after a
successful handshake. `"unknown"` is returned only in the unexpected case that OpenSSL reports no
version at all.
-/
@[extern "lean_ssl_negotiated_version"]
opaque negotiatedVersion (ssl : @& Session) : IO String

/--
Sends a TLS `close_notify` alert via `SSL_shutdown`.
- Returns `none` when the bidirectional shutdown is complete.
- Returns `some .read` when our alert has been sent and we are waiting for the peer's `close_notify`;
the caller should drain the output BIO, wait for more encrypted input, then call `closeNotify` again.
If the peer's `close_notify` is already buffered, a single call may still return `none`.
- Returns `some .write` when OpenSSL still has encrypted output to drain before it can finish the
shutdown.
-/
@[extern "lean_ssl_close_notify"]
opaque closeNotify (ssl : @& Session) : IO (Option IOWant)

namespace Server

/--
Runs one handshake step on a server session.
-/
@[inline]
def handshake (s : Session.Server) : IO (Option IOWant) := Session.handshake s.toSession

/--
Writes plaintext into a server session.
-/
@[inline]
def write (s : Session.Server) (data : @& ByteArray) : IO (Option IOWant) := Session.write s.toSession data

/--
Reads decrypted plaintext from a server session.
-/
@[inline]
def read? (s : Session.Server) (maxBytes : UInt64) : IO ReadResult := Session.read? s.toSession maxBytes

/--
Feeds encrypted bytes into a server session's input BIO.
-/
@[inline]
def feedEncrypted (s : Session.Server) (data : @& ByteArray) : IO UInt64 := Session.feedEncrypted s.toSession data

/--
Drains encrypted bytes from a server session's output BIO.
-/
@[inline]
def drainEncrypted (s : Session.Server) : IO ByteArray := Session.drainEncrypted s.toSession

/--
Returns encrypted bytes pending in a server session's output BIO.
-/
@[inline]
def pendingEncrypted (s : Session.Server) : IO UInt64 := Session.pendingEncrypted s.toSession

/--
Returns plaintext bytes buffered in a server session.
-/
@[inline]
def pendingPlaintext (s : Session.Server) : IO UInt64 := Session.pendingPlaintext s.toSession

/--
Returns the X.509 verification result code for a server session.
-/
@[inline]
def verifyResult (s : Session.Server) : IO UInt64 := Session.verifyResult s.toSession

/--
Returns the X.509 verification result string for a server session.
-/
@[inline]
def verifyResultString (s : Session.Server) : IO String := Session.verifyResultString s.toSession

/--
Sends a TLS `close_notify` alert on a server session.
-/
@[inline]
def closeNotify (s : Session.Server) : IO (Option IOWant) := Session.closeNotify s.toSession

/--
Returns the negotiated TLS version string for a server session.
-/
@[inline]
def negotiatedVersion (s : Session.Server) : IO String := Session.negotiatedVersion s.toSession

end Server

namespace Client

/--
Sets the server name for the client TLS handshake.

This sets both the SNI extension sent in the ClientHello and enables post-handshake hostname
verification against the certificate CN/SAN. Without it, OpenSSL validates only the certificate
chain — not that the certificate belongs to the host being connected to. Must be called before the
handshake.
-/
def setServerName (s : Session.Client) (host : @& String) : IO Unit := Session.setServerNameImpl s.toSession host

/--
Runs one handshake step on a client session.
-/
@[inline]
def handshake (s : Session.Client) : IO (Option IOWant) := Session.handshake s.toSession

/--
Writes plaintext into a client session.
-/
@[inline]
def write (s : Session.Client) (data : @& ByteArray) : IO (Option IOWant) := Session.write s.toSession data

/--
Reads decrypted plaintext from a client session.
-/
@[inline]
def read? (s : Session.Client) (maxBytes : UInt64) : IO ReadResult := Session.read? s.toSession maxBytes

/--
Feeds encrypted bytes into a client session's input BIO.
-/
@[inline]
def feedEncrypted (s : Session.Client) (data : @& ByteArray) : IO UInt64 := Session.feedEncrypted s.toSession data

/--
Drains encrypted bytes from a client session's output BIO.
-/
@[inline]
def drainEncrypted (s : Session.Client) : IO ByteArray := Session.drainEncrypted s.toSession

/--
Returns encrypted bytes pending in a client session's output BIO.
-/
@[inline]
def pendingEncrypted (s : Session.Client) : IO UInt64 := Session.pendingEncrypted s.toSession

/--
Returns plaintext bytes buffered in a client session.
-/
@[inline]
def pendingPlaintext (s : Session.Client) : IO UInt64 := Session.pendingPlaintext s.toSession

/--
Returns the X.509 verification result code for a client session.
-/
@[inline]
def verifyResult (s : Session.Client) : IO UInt64 := Session.verifyResult s.toSession

/--
Returns the X.509 verification result string for a client session.
-/
@[inline]
def verifyResultString (s : Session.Client) : IO String := Session.verifyResultString s.toSession

/--
Sends a TLS `close_notify` alert on a client session.
-/
@[inline]
def closeNotify (s : Session.Client) : IO (Option IOWant) := Session.closeNotify s.toSession

/--
Returns the negotiated TLS version string for a client session.
-/
@[inline]
def negotiatedVersion (s : Session.Client) : IO String := Session.negotiatedVersion s.toSession

end Client
end Session
end Std.Internal.SSL

end
