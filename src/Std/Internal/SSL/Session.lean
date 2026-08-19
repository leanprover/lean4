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
(`feedEncrypted`, `drainEncrypted`) and plaintext I/O (`write`, `read?`). The session drives no
transport of its own: the caller moves the encrypted bytes to and from whatever socket it uses.
-/

public section

namespace Std.Internal.SSL

private opaque SessionImpl : NonemptyType.{0}

/--
Represents an OpenSSL SSL session. Use `Session.Server.mk` / `Session.Client.mk` to create
role-specific sessions.

A session is not safe for concurrent use. Operations on the same session from more than one task
have to be serialized externally, for example with a `Std.Mutex`.
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
  OpenSSL needs socket I/O before it can produce plaintext.
  -/
  | wantIO (want : IOWant)

  /--
  The peer closed the TLS session cleanly (`SSL_ERROR_ZERO_RETURN`).
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
Gets the X.509 verification result code after the handshake (`0` is `X509_V_OK`).

OpenSSL also returns `X509_V_OK` when the peer presented no certificate at all, and on a session
that has not handshaked yet, so a `0` result does not by itself prove an authenticated peer; read it
only after a successful handshake, and confirm a certificate was received when that matters.
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

Each step is the main producer of handshake output, so always `drainEncrypted` afterwards whatever
the result: waiting for the reported I/O without sending the flight it just produced deadlocks the
session.

A `none` says the handshake is done, not that the session has nothing left to send: plaintext
queued by a `write` issued before the handshake stays queued, since only `write`, `closeNotify`
and a `read?` that reports `.wantIO` flush that queue. Follow a completed handshake with
`write ByteArray.empty` unless `write` or `closeNotify` is the next call anyway.

Raises once the session has finished, including `IO.Error.unexpectedEof` when the input stream was
found truncated.
-/
@[extern "lean_ssl_handshake"]
opaque handshake (ssl : @& Session) : IO (Option IOWant)

/--
Attempts to write plaintext application data into SSL. Returns `none` when all queued plaintext
(including `data`) has been accepted. Returns `some w` when OpenSSL needs socket I/O of kind `w`
before the write can complete; in that case the data has been queued internally and **must not** be
submitted again — call `write` again with an empty `data` once the I/O is satisfied to keep draining
the queue.

Every result may leave encrypted output behind, `some .read` included: a write that blocks does so
because it drove a handshake step, which puts a flight in the output BIO that has to reach the peer
before the awaited input can arrive. Always `drainEncrypted` after a `write`; waiting for the
reported I/O without draining first deadlocks the session.

Passing an empty `data` does not enqueue anything: it only flushes any previously queued plaintext
and reports whether the queue is now drained (`none`) or still blocked (`some w`).

The internal queue is bounded (1 MiB), so writing repeatedly while blocked eventually raises
`IO.Error.resourceExhausted` rather than buffering without limit; a payload rejected that way is not
queued, and the caller retries it once the I/O reported by the preceding `write` has completed.

The bound is checked only while the queue is still blocked. A `data` larger than it is therefore
accepted whenever the queue is empty by the time OpenSSL sees it — including when a queue that was
non-empty drains first — because OpenSSL then asks for that exact payload back and it has to be
kept. Nothing further is admitted until the queue drains, so the queue holds at most one such
payload rather than the bound plus one.

Raises `IO.Error.invalidArgument` if `data` is larger than `Int32.maxValue` bytes, and once the
session has finished, including `IO.Error.unexpectedEof` when the input stream was found truncated.

Raises `IO.Error.resourceExhausted` if `data` cannot be buffered at all, which leaves the session
usable and `data` unqueued exactly like the bound above. The one exception is a payload OpenSSL has
asked to have replayed verbatim: nothing can present those bytes again, so failing to buffer them
finishes the session.

Raises `IO.Error.protocolError` for a non-empty `data` once `closeNotify` has sent our alert, since
that closes the write direction; an empty `data` still reports the state of the queue as above. The
session is left usable rather than finished: the peer may have sent records before it saw the alert,
and `read?` is still the way to collect them.
-/
@[extern "lean_ssl_write"]
opaque write (ssl : @& Session) (data : @& ByteArray) : IO (Option IOWant)

/--
Attempts to read decrypted plaintext data.

At most 16 KiB (`SSL3_RT_MAX_PLAIN_LENGTH`, one TLS record's worth of plaintext) is returned per
call, regardless of `maxBytes`; call again to read further data.

When `maxBytes == 0`, performs a peek: returns `.data ByteArray.empty` if any plaintext is available
(without consuming it), `.closed` if the peer has sent `close_notify`, or `.wantIO` if more socket
I/O is needed first. Only the plaintext is left untouched — like any other read, a peek drives the
session, so on a session that has not handshaked yet it starts the handshake and thereby makes a
later `Client.setServerName` raise. Configure the server name before the first read of any kind.

Before reporting `.wantIO`, this flushes any plaintext still queued by `write`, so a `.wantIO .read`
may come back with fresh encrypted output waiting: always `drainEncrypted` after a `read?` rather
than only when the result asks for `.write`. A failure of that flush is raised from here. A `read?`
that returns `.data` or `.closed` does not flush, so use `write ByteArray.empty` when the queue has
to drain regardless.

Raises once the session has finished, and `IO.Error.unexpectedEof` when the input stream was found
truncated.
-/
@[extern "lean_ssl_read"]
opaque read? (ssl : @& Session) (maxBytes : UInt64) : IO ReadResult

/--
Feeds encrypted TLS bytes into the SSL input BIO and returns the number of bytes written.

The input BIO is an in-memory BIO, which never performs a short write: this consumes all of `data`
(so the result always equals `data.size`) or raises on a fatal BIO error.

Raises `IO.Error.invalidArgument` if `feedEof` has already been called, or if `data` is larger than
`Int32.maxValue` bytes. The `feedEof` check comes first, so a session that is both ended and
finished reports that rather than the failure below.

Raises `IO.Error.protocolError` once the session has finished, not `invalidArgument`, since nothing
consumes the input BIO after that and accepting more would grow it without bound. A truncated stream
always reports the `feedEof` case above instead, since only `feedEof` can produce one.
-/
@[extern "lean_ssl_feed_encrypted"]
opaque feedEncrypted (ssl : @& Session) (data : @& ByteArray) : IO UInt64

/--
Reports that the transport carrying the encrypted stream has reached end of file, so no further
`feedEncrypted` will follow. Call this when the socket read side closes.

Without it a session cannot distinguish "no bytes have arrived yet" from "no bytes will ever
arrive": a peer that drops the connection without sending `close_notify` leaves `read?` reporting
`.wantIO .read` indefinitely. Once this is called, `read?` drains whatever was already fed and then
raises `IO.Error.unexpectedEof` — the truncation that a stripped `close_notify` produces — or
returns `.closed` if the peer's `close_notify` did arrive. A truncated stream keeps reporting
`IO.Error.unexpectedEof` on every later `read?`, so the diagnosis does not depend on which call
observes it first.

This is also what settles a `closeNotify` the peer never answered: without it such a shutdown keeps
reporting `some .read`, and after it the next call reports `none`.

Bytes fed earlier stay readable; the end of file only takes effect once they are consumed. Calling
this more than once is harmless, but `feedEncrypted` afterwards raises.
-/
@[extern "lean_ssl_feed_eof"]
opaque feedEof (ssl : @& Session) : IO Unit

/--
Drains encrypted TLS bytes from the SSL output BIO.

Like the other operations that do not check the session state — `pendingEncrypted`,
`pendingPlaintext`, `verifyResult`, `verifyResultString`, `negotiatedVersion` and `feedEof` — this
keeps working on a session that has finished, so a teardown path can still send the alert a failed
`closeNotify` left behind.
-/
@[extern "lean_ssl_drain_encrypted"]
opaque drainEncrypted (ssl : @& Session) : IO ByteArray

/--
Returns the amount of encrypted TLS bytes currently pending in the output BIO.
-/
@[extern "lean_ssl_pending_encrypted"]
opaque pendingEncrypted (ssl : @& Session) : IO UInt64

/--
Returns the amount of plaintext already decrypted and not yet consumed, which the next `read?` calls
can return without needing more encrypted input.

Because it covers only what has been decrypted, `0` does not mean the session is drained: records
that have been fed but not yet opened report `0` and still yield data. Use `read?` itself to decide
whether anything is left.
-/
@[extern "lean_ssl_pending_plaintext"]
opaque pendingPlaintext (ssl : @& Session) : IO UInt64

/--
Returns the negotiated TLS protocol version string, e.g. `"TLSv1.3"` or `"TLSv1.2"`.

Only meaningful after a successful handshake. A session that has not been driven yet answers
`"TLSv1.3"` whatever the peer turns out to support and whatever bounds the context sets; from the
first `handshake` step until the handshake completes it reports the highest version the context
allows, which is still not what the peer agreed to.
-/
@[extern "lean_ssl_negotiated_version"]
opaque negotiatedVersion (ssl : @& Session) : IO String

/--
Sends a TLS `close_notify` alert via `SSL_shutdown`.
- Returns `none` when nothing is left to do: normally because the bidirectional shutdown is
complete, and also for a session that never had one to run (see below).
- Returns `some .read` when more encrypted input is genuinely needed before the shutdown can finish,
normally because our alert has been sent and the peer's `close_notify` has not arrived; the caller
should drain the output BIO, wait for more encrypted input, then call `closeNotify` again. If the
peer's `close_notify` is already buffered, a single call may still return `none`.
- Returns `some .write` when OpenSSL needs to flush encrypted output before it can finish the
shutdown. The output BIO is memory-backed and never blocks, so this does not arise today; drain
after every call regardless of the result, since the alert itself is output that has to be sent.

Every `IOWant` reported here names socket I/O the transport can still satisfy, including one this
layer names itself where OpenSSL reports none. It is not a promise that the peer will answer:
against a peer that sends nothing further this keeps reporting `some .read`, and it is `feedEof` —
reporting that the transport itself ended — that lets the next call settle the shutdown. A caller
looping on this needs one or the other, and should bound the wait.

On a session whose handshake has completed, plaintext still queued by `write` is flushed before the
alert is sent, so a shutdown never drops accepted data; while that flush is blocked this returns the
`IOWant` it is waiting on and sends nothing.

Unread plaintext from the peer stops the shutdown short of its alert, which sits behind that
plaintext where only `read?` can reach it. Such a session reports `none`: our alert has been sent,
and no socket I/O can carry the shutdown past data already in hand, so there is no `IOWant` to
report.
Drain the session with `read?` before shutting it down when a full bidirectional shutdown matters —
after the plaintext and the peer's `close_notify` have been read, a further call reports `none`
having completed it. The plaintext is never consumed or discarded by this, and `read?` keeps working
after our `close_notify` has been sent, since a peer may legitimately have sent records before it
saw our alert. Only `write` stops working: the alert closes the write direction alone, so it raises
without finishing the session.

A session with nothing left to tear down — the handshake was never run, a fatal error tore it down,
or the transport ended before the peer's `close_notify` arrived — has nothing to close and returns
`none` rather than raising, so teardown paths can call this unconditionally. This holds whether or
not an earlier call had already diagnosed the condition; a shutdown never reports one of these
itself, since there is nothing left to shut down either way. Such a session is left marked as
finished, so a later `handshake`, `write`, `read?`, `feedEncrypted` or `setServerName` raises
instead of driving a session this already reported closed. Those calls report a session closed
before it ever negotiated as such, rather than as a fatal error it never hit — unless the transport
was also found truncated, which keeps its own `IO.Error.unexpectedEof`.

A peer that sends its `close_notify` in the middle of a post-handshake message it never finished
also leaves nothing to close, and this reports `none`. Neither alert can be exchanged from there,
however much input follows. That session is *not* marked as finished, since it closed cleanly, and
`read?` goes on to report `.closed`. Only `drainEncrypted` is still worth calling beyond that: once
the peer's alert has been processed OpenSSL answers every read with it, so nothing fed afterwards can
be consumed.

The one exception is plaintext `write` accepted but never delivered: such a session cannot carry it,
and this raises rather than reporting a clean close. The loss is reported once — the queue is
dropped as it is reported — so a teardown path that calls this again gets the clean `none`. Beyond
that, only a fatal failure of the shutdown itself raises.
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
Feeds encrypted bytes into a server session's input BIO.
-/
@[inline]
def feedEncrypted (s : @& Session.Server) (data : @& ByteArray) : IO UInt64 := Session.feedEncrypted s.toSession data

/--
Reports end of file on the transport feeding a server session.
-/
@[inline]
def feedEof (s : @& Session.Server) : IO Unit := Session.feedEof s.toSession

/--
Drains encrypted bytes from a server session's output BIO.
-/
@[inline]
def drainEncrypted (s : @& Session.Server) : IO ByteArray := Session.drainEncrypted s.toSession

/--
Returns encrypted bytes pending in a server session's output BIO.
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
Sets the server name for the client TLS handshake.

This sets both the SNI extension sent in the ClientHello and the reference identity the peer's
certificate is checked against during the handshake. Without it, OpenSSL validates only the
certificate chain — not that the certificate belongs to the host being connected to.

The SNI extension travels in the `ClientHello`, so this raises once the handshake has started rather
than silently sending the peer one name and verifying against another. It also raises
`IO.Error.invalidArgument` for a host that cannot be used, such as one containing NUL bytes, one
that is empty, or one that is too long for SNI. An empty host is refused rather than treated as "no
name", which would leave the certificate verified against nothing.

A rejected host is never left half-applied in a direction that could send the peer a name this is
not going to verify against, but it may withdraw a name set by an earlier call. If binding the host
for verification is what failed, the session is left with nothing to verify against and is finished,
so a later `handshake`, `write`, `read?`, `feedEncrypted` or `setServerName` raises rather than
running a handshake that checks the chain alone. Teardown is unaffected: `closeNotify` and
`drainEncrypted` keep working, as they do on any finished session.

This only takes effect on a client context created with `verifyPeer := true`. Without it OpenSSL
still runs the check and records the verdict in `verifyResult`, but completes the handshake
regardless, so the name is not enforced.

An IP address in textual form is accepted and verified against the certificate's `iPAddress` SANs,
in the bare form and in the bracketed one a URI authority spells IPv6 with (`[::1]`). No SNI is
sent for one: RFC 6066 §3 forbids a literal address there, and peers that enforce it answer
`unrecognized_name`. Verification is unaffected — only the extension is omitted.

A single trailing dot is stripped: it spells an absolute FQDN, which RFC 6066 §3 forbids in SNI and
which OpenSSL matches against no certificate, so the peer sees — and the certificate is verified
against — the name without it.

Calling this more than once replaces the previous name rather than adding to it, so a name set and
then changed does not leave the earlier one being verified against as well.
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
Feeds encrypted bytes into a client session's input BIO.
-/
@[inline]
def feedEncrypted (s : @& Session.Client) (data : @& ByteArray) : IO UInt64 := Session.feedEncrypted s.toSession data

/--
Reports end of file on the transport feeding a client session.
-/
@[inline]
def feedEof (s : @& Session.Client) : IO Unit := Session.feedEof s.toSession

/--
Drains encrypted bytes from a client session's output BIO.
-/
@[inline]
def drainEncrypted (s : @& Session.Client) : IO ByteArray := Session.drainEncrypted s.toSession

/--
Returns encrypted bytes pending in a client session's output BIO.
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
