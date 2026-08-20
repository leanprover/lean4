/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module
prelude
public import Std.Internal.SSL.Context

/-!
Low-level OpenSSL session API: a TLS state machine with explicit encrypted I/O (`feedEncrypted`,
`drainEncrypted`) and plaintext I/O (`write`, `read?`). The session drives no transport of its own:
the caller moves the encrypted bytes to and from whatever socket it uses.

No session here is safe for concurrent use. Operations on the same session from more than one task
have to be serialized externally, for example with a `Std.Mutex`.
-/

public section

namespace Std.Internal.SSL

private opaque SessionImpl : NonemptyType.{0}

/--
Represents an OpenSSL SSL session, which is not safe for concurrent use. Use `Session.Server.mk` /
`Session.Client.mk` to create role-specific sessions.
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
  More encrypted bytes are needed from the socket.
  -/
  | read

  /--
  Encrypted bytes have to be flushed to the socket.
  -/
  | write
  deriving Repr, DecidableEq, Inhabited

/--
Result of a `Session.read?` call.
-/
inductive ReadResult where

  /--
  Plaintext data was successfully decrypted.
  -/
  | data (bytes : ByteArray)

  /--
  Socket I/O is needed before plaintext can be produced.
  -/
  | wantIO (want : IOWant)

  /--
  The peer closed the TLS session cleanly.
  -/
  | closed
  deriving Inhabited

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
Gets the X.509 verification result code after the handshake, where `0` means the peer's certificate
verified. A peer that presented no certificate at all also reports `0`, so this alone does not prove
an authenticated peer.
-/
@[extern "lean_ssl_verify_result"]
opaque verifyResult (ssl : @& Session) : IO UInt64

/--
Gets the human-readable X.509 verify result string after handshake.
-/
@[extern "lean_ssl_verify_result_string"]
opaque verifyResultString (ssl : @& Session) : IO String

/--
Runs one handshake step. Returns `none` when the handshake is complete, or `some w` when socket I/O
of kind `w` is needed first. Always `drainEncrypted` afterwards whatever the result: waiting for the
reported I/O without sending what the step produced deadlocks the session. Raises once the session
has finished, including `IO.Error.unexpectedEof` on a truncated input stream.
-/
@[extern "lean_ssl_handshake"]
opaque handshake (ssl : @& Session) : IO (Option IOWant)

/--
Writes plaintext application data. Returns `none` when everything written so far has been encrypted,
or `some w` when socket I/O of kind `w` is needed to finish. `data` is accepted either way, so never
pass it again: retry with `write ByteArray.empty` after the I/O until it reports `none`. Always
`drainEncrypted` afterwards whatever the result. Raises `IO.Error.resourceExhausted` if too much
plaintext is already waiting to be encrypted, in which case `data` was not accepted and can be
passed again later; `IO.Error.invalidArgument` for a `data` larger than `Int32.maxValue` bytes;
`IO.Error.protocolError` for a non-empty `data` after `closeNotify`, which closes the write
direction alone and leaves `read?` usable; and once the session has finished, including
`IO.Error.unexpectedEof` on a truncated input stream.
-/
@[extern "lean_ssl_write"]
opaque write (ssl : @& Session) (data : @& ByteArray) : IO (Option IOWant)

/--
Reads decrypted plaintext data. At most 16 KiB — one TLS record's worth — is returned per call
regardless of `maxBytes`; call again for more. A `maxBytes` of `0` peeks: `.data ByteArray.empty` if
plaintext is available without consuming it, `.closed` after the peer's `close_notify`, `.wantIO` if
socket I/O is needed first. A peek still drives the session, so it starts the handshake on a fresh
one and thereby makes a later `Client.setServerName` raise — configure the server name before any
read. Always `drainEncrypted` afterwards, since a read may produce output of its own. Raises once
the session has finished, and `IO.Error.unexpectedEof` on a truncated input stream.
-/
@[extern "lean_ssl_read"]
opaque read? (ssl : @& Session) (maxBytes : UInt64) : IO ReadResult

/--
Feeds encrypted TLS bytes received from the peer into the session, returning the number of bytes
taken. All of `data` is consumed, so the result always equals `data.size`. Raises
`IO.Error.invalidArgument` after `feedEof`, or for a `data` larger than `Int32.maxValue` bytes, and
`IO.Error.protocolError` once the session has finished.
-/
@[extern "lean_ssl_feed_encrypted"]
opaque feedEncrypted (ssl : @& Session) (data : @& ByteArray) : IO UInt64

/--
Reports that the transport carrying the encrypted stream has reached end of file. Call this when the
socket read side closes: without it a peer that drops the connection without sending `close_notify`
leaves `read?` and `closeNotify` waiting on input that will never arrive. Bytes fed earlier stay
readable, and once they are consumed `read?` reports `.closed` if the peer's `close_notify` did
arrive, or raises `IO.Error.unexpectedEof` for the truncated stream if it did not. Calling this more
than once is harmless, but `feedEncrypted` afterwards raises.
-/
@[extern "lean_ssl_feed_eof"]
opaque feedEof (ssl : @& Session) : IO Unit

/--
Drains the encrypted TLS bytes waiting to be sent to the peer. This works on a session that has
finished, so a teardown path can still send the alert a failed `closeNotify` left behind.
-/
@[extern "lean_ssl_drain_encrypted"]
opaque drainEncrypted (ssl : @& Session) : IO ByteArray

/--
Returns the amount of encrypted TLS bytes currently waiting to be sent to the peer.
-/
@[extern "lean_ssl_pending_encrypted"]
opaque pendingEncrypted (ssl : @& Session) : IO UInt64

/--
Returns the amount of plaintext the next `read?` calls can return without needing more encrypted
input. A `0` does not mean the session is drained, since bytes already fed may still decrypt to
plaintext; use `read?` itself to decide whether anything is left.
-/
@[extern "lean_ssl_pending_plaintext"]
opaque pendingPlaintext (ssl : @& Session) : IO UInt64

/--
Returns the negotiated TLS protocol version string, e.g. `"TLSv1.3"` or `"TLSv1.2"`. Only meaningful
after a successful handshake; before the handshake completes it reports a version the context
allows rather than one the peer agreed to.
-/
@[extern "lean_ssl_negotiated_version"]
opaque negotiatedVersion (ssl : @& Session) : IO String

/--
Sends a TLS `close_notify` alert.
- Returns `none` when nothing is left to do: the bidirectional shutdown is complete, or the session
never had one to run.
- Returns `some .read` when more encrypted input is needed to finish, normally because our alert has
been sent and the peer's has not arrived; drain the encrypted output, wait for input, and call again.
- Returns `some .write` when encrypted output has to be flushed before the shutdown can finish.

Always `drainEncrypted` afterwards, since the alert itself is output that has to be sent. An `IOWant`
is not a promise that the peer will answer: against a silent peer this keeps reporting `some .read`
until `feedEof` reports the transport ended, so bound the wait when looping on it. Read the session
to `.closed` first when a full bidirectional shutdown matters — unread plaintext hides the peer's
alert behind it, and this reports `none` without waiting for what it cannot reach. Afterwards `read?`
still works, since the peer may have sent records before it saw the alert, and only `write` raises.
A session with nothing left to tear down returns `none` rather than raising, so teardown paths can
call this unconditionally. It raises only on a fatal shutdown failure, or when plaintext accepted by
`write` can no longer be delivered — reported once, so a second call gets the clean `none`.
-/
@[extern "lean_ssl_close_notify"]
opaque closeNotify (ssl : @& Session) : IO (Option IOWant)

namespace Server

/--
Runs one handshake step on a server session.
-/
@[inline]
def handshake (s : @& Session.Server) : IO (Option IOWant) := Session.handshake s.toSession

/--
Writes plaintext into a server session.
-/
@[inline]
def write (s : @& Session.Server) (data : @& ByteArray) : IO (Option IOWant) := Session.write s.toSession data

/--
Reads decrypted plaintext from a server session.
-/
@[inline]
def read? (s : @& Session.Server) (maxBytes : UInt64) : IO ReadResult := Session.read? s.toSession maxBytes

/--
Feeds encrypted bytes into a server session.
-/
@[inline]
def feedEncrypted (s : @& Session.Server) (data : @& ByteArray) : IO UInt64 := Session.feedEncrypted s.toSession data

/--
Reports end of file on the transport feeding a server session.
-/
@[inline]
def feedEof (s : @& Session.Server) : IO Unit := Session.feedEof s.toSession

/--
Drains the encrypted bytes a server session has waiting for the peer.
-/
@[inline]
def drainEncrypted (s : @& Session.Server) : IO ByteArray := Session.drainEncrypted s.toSession

/--
Returns the encrypted bytes a server session has waiting for the peer.
-/
@[inline]
def pendingEncrypted (s : @& Session.Server) : IO UInt64 := Session.pendingEncrypted s.toSession

/--
Returns plaintext bytes buffered in a server session.
-/
@[inline]
def pendingPlaintext (s : @& Session.Server) : IO UInt64 := Session.pendingPlaintext s.toSession

/--
Returns the X.509 verification result code for a server session.
-/
@[inline]
def verifyResult (s : @& Session.Server) : IO UInt64 := Session.verifyResult s.toSession

/--
Returns the X.509 verification result string for a server session.
-/
@[inline]
def verifyResultString (s : @& Session.Server) : IO String := Session.verifyResultString s.toSession

/--
Sends a TLS `close_notify` alert on a server session.
-/
@[inline]
def closeNotify (s : @& Session.Server) : IO (Option IOWant) := Session.closeNotify s.toSession

/--
Returns the negotiated TLS version string for a server session.
-/
@[inline]
def negotiatedVersion (s : @& Session.Server) : IO String := Session.negotiatedVersion s.toSession

end Server

namespace Client

/--
Sets both the SNI extension sent in the `ClientHello` and the reference identity the peer's
certificate is verified against; without it only the certificate chain is validated, not that the
certificate belongs to the host being connected to, and it is enforced only on a context created
with `verifyPeer := true`. Since SNI travels in the `ClientHello`, this has to be called before the
first `handshake` or `read?` and raises afterwards. It raises `IO.Error.invalidArgument` for a host
that cannot be used: one containing NUL bytes, one that is empty, or one too long for SNI. A textual
IP address is accepted, bare or in the bracketed form a URI authority spells IPv6 with (`[::1]`),
and verified against the certificate's `iPAddress` SANs, but no SNI is sent for one, since RFC 6066
§3 forbids a literal address there. A single trailing dot is stripped for the same reason, so the
peer sees — and the certificate is verified against — the name without it. Calling this again
replaces the previous name rather than adding to it.
-/
@[inline]
def setServerName (s : @& Session.Client) (host : @& String) : IO Unit := Session.setServerNameImpl s.toSession host

/--
Runs one handshake step on a client session.
-/
@[inline]
def handshake (s : @& Session.Client) : IO (Option IOWant) := Session.handshake s.toSession

/--
Writes plaintext into a client session.
-/
@[inline]
def write (s : @& Session.Client) (data : @& ByteArray) : IO (Option IOWant) := Session.write s.toSession data

/--
Reads decrypted plaintext from a client session.
-/
@[inline]
def read? (s : @& Session.Client) (maxBytes : UInt64) : IO ReadResult := Session.read? s.toSession maxBytes

/--
Feeds encrypted bytes into a client session.
-/
@[inline]
def feedEncrypted (s : @& Session.Client) (data : @& ByteArray) : IO UInt64 := Session.feedEncrypted s.toSession data

/--
Reports end of file on the transport feeding a client session.
-/
@[inline]
def feedEof (s : @& Session.Client) : IO Unit := Session.feedEof s.toSession

/--
Drains the encrypted bytes a client session has waiting for the peer.
-/
@[inline]
def drainEncrypted (s : @& Session.Client) : IO ByteArray := Session.drainEncrypted s.toSession

/--
Returns the encrypted bytes a client session has waiting for the peer.
-/
@[inline]
def pendingEncrypted (s : @& Session.Client) : IO UInt64 := Session.pendingEncrypted s.toSession

/--
Returns plaintext bytes buffered in a client session.
-/
@[inline]
def pendingPlaintext (s : @& Session.Client) : IO UInt64 := Session.pendingPlaintext s.toSession

/--
Returns the X.509 verification result code for a client session.
-/
@[inline]
def verifyResult (s : @& Session.Client) : IO UInt64 := Session.verifyResult s.toSession

/--
Returns the X.509 verification result string for a client session.
-/
@[inline]
def verifyResultString (s : @& Session.Client) : IO String := Session.verifyResultString s.toSession

/--
Sends a TLS `close_notify` alert on a client session.
-/
@[inline]
def closeNotify (s : @& Session.Client) : IO (Option IOWant) := Session.closeNotify s.toSession

/--
Returns the negotiated TLS version string for a client session.
-/
@[inline]
def negotiatedVersion (s : @& Session.Client) : IO String := Session.negotiatedVersion s.toSession

end Client
end Session
end Std.Internal.SSL

end
