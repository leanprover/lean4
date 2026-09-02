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
`drainEncrypted`) and plaintext I/O (`write`, `read`). The session drives no transport of its own:
the caller moves the encrypted bytes to and from whatever socket it uses.

No session here is safe for concurrent use. Operations on the same session from more than one task
have to be serialized externally, for example with a `Std.Mutex`.
-/

public section

namespace Std.Internal.SSL

private opaque SessionImpl : NonemptyType.{0}

/--
Which side of the handshake a session drives.
-/
inductive Session.Role where

  /--
  Answers a `ClientHello` and presents a certificate.
  -/
  | server

  /--
  Opens the handshake and verifies the peer.
  -/
  | client
  deriving Repr, DecidableEq, Inhabited

/--
The runtime handle a `Session` carries.
-/
def Session.Core : Type := SessionImpl.type

instance : Nonempty Session.Core := SessionImpl.property

/--
An OpenSSL TLS session: a state machine fed encrypted bytes from the peer and drained of the
encrypted bytes to send back. `role` keeps the two sides apart at the type level, so a server
session cannot be passed where a client one is required.

Not safe for concurrent use. Use `Session.Server.mk` / `Session.Client.mk` to create one.
-/
structure Session (role : Session.Role) where
  private ofCore ::
  /--
  The underlying runtime handle.
  -/
  core : Session.Core

instance : Nonempty (Session role) := Nonempty.elim SessionImpl.property fun c => ⟨⟨c⟩⟩

/--
A server-side TLS session.
-/
abbrev Session.Server := Session .server

/--
A client-side TLS session.
-/
abbrev Session.Client := Session .client

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
Result of a `Session.read` call.
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

namespace Session

@[extern "lean_ssl_mk_server"]
private opaque mkServerImpl (ctx : @& Context.Server) : IO Core

@[extern "lean_ssl_mk_client"]
private opaque mkClientImpl (ctx : @& Context.Client) : IO Core

@[extern "lean_ssl_set_server_name"]
private opaque setServerNameImpl (ssl : @& Core) (host : @& String) : IO Unit

@[extern "lean_ssl_verify_result"]
private opaque verifyResultImpl (ssl : @& Core) : IO UInt64

@[extern "lean_ssl_verify_result_string"]
private opaque verifyResultStringImpl (ssl : @& Core) : IO String

@[extern "lean_ssl_handshake"]
private opaque handshakeImpl (ssl : @& Core) : IO (Option IOWant)

@[extern "lean_ssl_write"]
private opaque writeImpl (ssl : @& Core) (data : @& ByteArray) : IO (Option IOWant)

@[extern "lean_ssl_read"]
private opaque readImpl (ssl : @& Core) (maxBytes : UInt64) : IO ReadResult

@[extern "lean_ssl_feed_encrypted"]
private opaque feedEncryptedImpl (ssl : @& Core) (data : @& ByteArray) : IO UInt64

@[extern "lean_ssl_feed_eof"]
private opaque feedEofImpl (ssl : @& Core) : IO Unit

@[extern "lean_ssl_drain_encrypted"]
private opaque drainEncryptedImpl (ssl : @& Core) : IO ByteArray

@[extern "lean_ssl_pending_encrypted"]
private opaque pendingEncryptedImpl (ssl : @& Core) : IO UInt64

@[extern "lean_ssl_pending_plaintext"]
private opaque pendingPlaintextImpl (ssl : @& Core) : IO UInt64

@[extern "lean_ssl_negotiated_version"]
private opaque negotiatedVersionImpl (ssl : @& Core) : IO String

@[extern "lean_ssl_close_notify"]
private opaque closeNotifyImpl (ssl : @& Core) : IO (Option IOWant)

namespace Server

/--
Creates a server-side TLS session from the given context. The context supplies the certificate the
server presents; it requests none from the client, so a server session never authenticates its peer
and `verifyResult` has nothing to report.
-/
def mk (ctx : @& Context.Server) : IO Session.Server :=
  return ⟨← mkServerImpl ctx⟩

end Server

namespace Client

/--
Creates a client-side TLS session from the given context, verifying the peer against `host`.

`host` is both the SNI extension sent in the `ClientHello` and the reference identity the peer's
certificate is checked against. It is enforced only on a context created with `verifyPeer := true`,
and it is set here rather than afterwards because SNI travels in the `ClientHello`: there is no
point at which a session exists and the name can still take effect.

A textual IP address is accepted, bare or in the bracketed form a URI authority spells IPv6 with
(`[::1]`), and is verified against the certificate's `iPAddress` SANs; no SNI is sent for one, since
RFC 6066 §3 forbids a literal address there. A single trailing dot is stripped, since neither SNI nor
a certificate SAN carries one, so the peer sees — and the certificate is verified against — the name
without it.

`none` binds no identity at all: the chain is still validated on a verifying context, but nothing
ties the certificate to the peer being talked to, so any certificate a trusted CA ever issued is
accepted. Pass it only where the peer is pinned some other way, and read `verifyResult` accordingly.

Raises `IO.Error.invalidArgument` for a host that cannot be used: one containing NUL bytes, one that
is empty, one bracketed that is not a valid IP address, or one too long for SNI.
-/
def mk (ctx : @& Context.Client) (host : Option String) : IO Session.Client := do
  let session : Session.Client := ⟨← mkClientImpl ctx⟩
  if let some host := host then
    setServerNameImpl session.core host
  return session

end Client

/--
Replaces the peer identity bound at construction: sets both the SNI extension for a handshake that
has not started yet and the reference identity the certificate is verified against. Restricted to a
client session, since a server sends no SNI and verifies no peer.

Accepts the same hosts as `Session.Client.mk`, and like it is enforced only on a context created with
`verifyPeer := true`. Both identity kinds are replaced, so a name never accumulates on top of an
address or the other way round. Raises `IO.Error.invalidArgument` once the handshake has started,
since SNI travels in the `ClientHello` and could no longer take effect.
-/
def setServerName (s : @& Session .client) (host : @& String) : IO Unit :=
  setServerNameImpl s.core host

/--
Gets the X.509 verification result code, where `0` means the peer's certificate verified.

This is a chain verdict alone. It reports `0` on a session that has not handshaked, on a peer that
presented no certificate, and on one whose certificate was never bound to a host — so it proves an
authenticated peer only for a client created with `verifyPeer := true` and a `host`. On a context
with `verifyPeer := false` the chain is still checked but not enforced, so a non-zero code there
says the handshake was allowed to proceed regardless.
-/
def verifyResult (s : @& Session role) : IO UInt64 := verifyResultImpl s.core

/--
Gets the human-readable X.509 verify result string, `"ok"` for a certificate that verified. Carries
the same caveats as `verifyResult`.
-/
def verifyResultString (s : @& Session role) : IO String := verifyResultStringImpl s.core

/--
Runs one handshake step. Returns `none` when the handshake is complete, or `some w` when socket I/O
of kind `w` is needed first. Always `drainEncrypted` afterwards whatever the result: waiting for the
reported I/O without sending what the step produced deadlocks the session.

A `none` says the handshake is done, not that the session has nothing left to send: plaintext queued
by a `write` issued before the handshake stays queued, since only `write`, `closeNotify` and a `read`
that reports `.wantIO` flush that queue. Follow a completed handshake with `write ByteArray.empty`
unless `write` or `closeNotify` is the next call anyway.

Raises once the session has finished, including `IO.Error.unexpectedEof` on a truncated input stream.
-/
def handshake (s : @& Session role) : IO (Option IOWant) := handshakeImpl s.core

/--
Writes plaintext application data. Returns `none` when everything written so far has been encrypted,
or `some w` when socket I/O of kind `w` is needed to finish. `data` is accepted either way, so never
pass it again: retry with `write ByteArray.empty` after the I/O until it reports `none`. Always
`drainEncrypted` afterwards whatever the result. A raise always leaves `data` unaccepted, so a
session that survives one holds no more plaintext than it did before the call.

Raises `IO.Error.resourceExhausted` for either of the two backlogs it bounds, and `data` can be
passed again once the backlog is gone:
- too much encrypted output is waiting to be sent, because `drainEncrypted` has not kept up. This is
the bound that matters on an established session, where encrypting never blocks and so nothing else
limits what a caller can accumulate by writing without draining. An empty `data` is always accepted,
since flushing is part of the way back under it.
- too much plaintext is waiting to be encrypted, which only happens while the session cannot encrypt
at all — before the handshake completes. The bound covers everything queued behind the first such
payload; that first one is retained whatever its size, since `SSL_write` requires it back verbatim.

Also raises `IO.Error.invalidArgument` for a `data` larger than `Int32.maxValue` bytes;
`IO.Error.protocolError` for a non-empty `data` after `closeNotify`, which closes the write direction
alone and leaves `read` usable; and once the session has finished, including
`IO.Error.unexpectedEof` on a truncated input stream.
-/
def write (s : @& Session role) (data : @& ByteArray) : IO (Option IOWant) := writeImpl s.core data

/--
Reads decrypted plaintext data. At most 16 KiB — one TLS record's worth — is returned per call
regardless of `maxBytes`; call again for more. A `maxBytes` of `0` peeks: `.data ByteArray.empty` if
plaintext is available without consuming it, `.closed` after the peer's `close_notify`, `.wantIO` if
socket I/O is needed first.

A `.wantIO` result also flushes the pending-write queue, so this can raise a failure of that flush
rather than of the read itself, and the `IOWant` it reports may be the queue's rather than the
read's. Always `drainEncrypted` afterwards, since a read may produce output of its own.

Raises once the session has finished, and `IO.Error.unexpectedEof` on a truncated input stream.
-/
def read (s : @& Session role) (maxBytes : UInt64) : IO ReadResult := readImpl s.core maxBytes

/--
Feeds encrypted TLS bytes received from the peer into the session, returning the number of bytes
taken. All of `data` is consumed, so the result always equals `data.size`.

Raises `IO.Error.invalidArgument` after `feedEof` or after the peer's `close_notify` — past either
point nothing will ever consume the bytes — for a `data` larger than `Int32.maxValue` bytes, and
once the session has finished, which reports `IO.Error.unexpectedEof` for a truncated stream and
`IO.Error.protocolError` otherwise.
-/
def feedEncrypted (s : @& Session role) (data : @& ByteArray) : IO UInt64 :=
  feedEncryptedImpl s.core data

/--
Reports that the transport carrying the encrypted stream has reached end of file. Call this when the
socket read side closes: without it a peer that drops the connection without sending `close_notify`
leaves `read` and `closeNotify` waiting on input that will never arrive. Bytes fed earlier stay
readable, and once they are consumed `read` reports `.closed` if the peer's `close_notify` did
arrive, or raises `IO.Error.unexpectedEof` for the truncated stream if it did not. Calling this more
than once is harmless, but `feedEncrypted` afterwards raises.
-/
def feedEof (s : @& Session role) : IO Unit := feedEofImpl s.core

/--
Drains the encrypted TLS bytes waiting to be sent to the peer. This works on a session that has
finished, so a teardown path can still send the alert a failed `closeNotify` left behind.
-/
def drainEncrypted (s : @& Session role) : IO ByteArray := drainEncryptedImpl s.core

/--
Returns the amount of encrypted TLS bytes currently waiting to be sent to the peer. `write` refuses
new plaintext once this grows too large, so a caller that keeps writing has to drain in step.
-/
def pendingEncrypted (s : @& Session role) : IO UInt64 := pendingEncryptedImpl s.core

/--
Returns the amount of plaintext the next `read` calls can return without needing more encrypted
input. A `0` does not mean the session is drained, since bytes already fed may still decrypt to
plaintext; use `read` itself to decide whether anything is left.
-/
def pendingPlaintext (s : @& Session role) : IO UInt64 := pendingPlaintextImpl s.core

/--
Returns the negotiated TLS protocol version string, e.g. `"TLSv1.3"` or `"TLSv1.2"`. Only meaningful
after a successful handshake; before the handshake completes it reports a version the context
allows rather than one the peer agreed to.
-/
def negotiatedVersion (s : @& Session role) : IO String := negotiatedVersionImpl s.core

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
alert behind it, and this reports `none` without waiting for what it cannot reach. Afterwards `read`
still works, since the peer may have sent records before it saw the alert, and only `write` raises.

A session with nothing left to tear down returns `none` rather than raising, so teardown paths can
call this unconditionally — but on one that never negotiated it also *finishes* the session, so every
call that drives it raises from then on, `drainEncrypted` still working so the alert can be sent. It
raises only on a fatal shutdown failure, or when plaintext accepted by `write` can no longer be
delivered — reported once, so a second call gets the clean `none`.
-/
def closeNotify (s : @& Session role) : IO (Option IOWant) := closeNotifyImpl s.core

end Session
end Std.Internal.SSL

end
