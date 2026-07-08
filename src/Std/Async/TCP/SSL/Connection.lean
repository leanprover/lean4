/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module
prelude
public import Std.Async.TCP.SSL.Basic

/-!
Operations on a TLS `Connection`: plaintext send/receive, the non-blocking `tryRecv`/`recvSelector`,
the TLS `close_notify` shutdown sequence, and the socket-level accessors shared by both client and
server connections.
-/

public section

namespace Std.Async.TCP.SSL

open Std.Internal.SSL
open Std.Internal.UV.TCP
open Std Net Time
open Internal

namespace Connection

/--
Sends data through a TLS-enabled socket until accepted. When OpenSSL reports the write as needing
additional I/O (e.g. during a renegotiation or before the handshake Finished round-trip completes),
this function performs the required socket I/O and retries until the data is accepted rather than throwing.

The plaintext is encrypted and flushed to the socket one `chunkSize` slice at a time, so peak
buffering stays bounded by roughly one chunk of ciphertext regardless of `data.size` and the socket
applies backpressure between slices.

If `timeout` is provided, each socket round-trip needed to complete the write must finish within that
duration or the function throws `"TLS operation timed out"`. Without a timeout, a stalled or malicious
peer that withholds the I/O needed to complete a renegotiation can block this call indefinitely. Note
that the timeout bounds each round-trip individually, not the whole operation: a peer that keeps
trickling bytes can still extend the total time without bound.

Any failure (including a timeout) marks the connection as broken. Throws if the connection is
already in a broken state from a previous failed operation; in either case the `Connection` must
be discarded.
-/
def send (s : Connection role) (data : ByteArray) (chunkSize : UInt64 := ioChunkSize)
    (timeout : Option Millisecond.Offset := none) : Async Unit := do
  withConnection s do
    let step := do
      match ← s.ssl.toSession.write ByteArray.empty with
      | none => return .done ()
      | some want => return .want want

    let sendChunk (chunk : ByteArray) : Async Unit := do
      let initial := match ← s.ssl.toSession.write chunk with
        | none => PumpStep.done ()
        | some want => PumpStep.want want

      let result ← pumpIO s.native s.ssl.toSession step chunkSize timeout
          "TLS write stalled: WANT_WRITE but output BIO produced no bytes" pure
          (throw <| IO.userError "connection closed while flushing TLS write")
          (initial? := some initial)

      match result with
      | .done () => return ()
      | .timedOut => throw <| IO.userError "TLS operation timed out"

    -- An empty send still runs one pump so previously queued plaintext gets flushed.
    let sliceLen := max 1 chunkSize.toNat
    let mut offset := 0
    sendChunk (data.extract offset sliceLen)
    offset := sliceLen

    while offset < data.size do
      sendChunk (data.extract offset (offset + sliceLen))
      offset := offset + sliceLen

/--
Sends multiple data buffers through the TLS-enabled socket. The `timeout`, if provided, applies to
each individual buffer's send.
-/
@[inline] def sendAll (s : Connection role) (data : Array ByteArray)
    (chunkSize : UInt64 := ioChunkSize) (timeout : Option Millisecond.Offset := none) : Async Unit :=
  data.forM (s.send · chunkSize timeout)

private def recvStep (s : Connection role) (size : UInt64) : IO (PumpStep (Option ByteArray)) := do
  match ← s.ssl.toSession.read? size with
  | .data plain => return .done (some plain)
  | .closed => return .done none
  | .wantIO want => return .want want

/--
Receives decrypted plaintext data from TLS. If no plaintext is immediately available, this function
performs the required socket I/O (flush or receive) and retries until data arrives or the connection
is closed.

Returns `none` only on a clean TLS close (the peer sent a `close_notify` alert). Passing `size = 0`
performs a non-consuming peek: it returns `some ByteArray.empty` when plaintext is pending (see
`Session.read?`).
-/
def recv? (s : Connection role) (size : UInt64) (chunkSize : UInt64 := ioChunkSize)
    (timeout : Option Millisecond.Offset := none) : Async (Option ByteArray) := do
  let result ← withConnection s <| pumpIO s.native s.ssl.toSession (recvStep s size) chunkSize timeout
    "TLS receive stalled: WANT_WRITE but output BIO produced no bytes" pure
    (throw <| IO.userError
      "TLS connection closed without close_notify (possible truncation attack)")
    (emptyWriteNeedsRead := true)
  match result with
  | .done value => return value
  | .timedOut => throw <| IO.userError "TLS operation timed out"

/--
Non-blocking receive of decrypted plaintext data.

- Returns `some (some data)` if plaintext is available.
- Returns `some none` if the peer closed the TLS session cleanly.
- Returns `none` if no plaintext is ready yet — the caller should wait and retry, not
  block. This is the non-blocking counterpart to `recv?`.

Passing `size = 0` performs a non-consuming peek: it returns `some (some ByteArray.empty)` when
plaintext is pending (see `Session.read?`).

A single `ssl.read?` drives the OpenSSL state machine without performing socket I/O, so it sees
plaintext from both the decrypted buffer (`SSL_pending`) and any encrypted bytes already pulled into
the input BIO (`BIO_pending`) but not yet decrypted. Checking only `SSL_pending` would miss the
latter, causing `recvSelector` to wait for new TCP data that will never arrive. Any plaintext
returned this way is consumed from the session, exactly as a successful `recv?` would consume it.

Throws if the connection is in a broken state from a previous failed operation.
-/
def tryRecv (s : Connection role) (size : UInt64) : Async (Option (Option ByteArray)) := do
  withConnection s do
    let step ← recvStep s size
    flushEncrypted s.native s.ssl.toSession
    match step with
    | .done value => return some value
    | .want _ => return none

/--
Creates a `Selector` that resolves once `s` has plaintext data available.

The race is won as soon as the underlying socket becomes readable; the selector then drives a full
`recv?` to completion before resolving. A timer raced against this selector via `Selectable.one`
therefore only bounds the time until the first encrypted bytes arrive, not until complete plaintext
is available — once the socket is readable, the race is committed and the timer can no longer fire.
For a hard bound on the whole receive, use `recv?` with its `timeout` parameter instead.
-/
def recvSelector (s : Connection role) (size : UInt64) : Selector (Option ByteArray) :=
  selectorFromWaiter (s.tryRecv size) s.native.waitReadable
    (fun _ => s.recv? size) s.native.cancelRecv

/--
Sends a TLS `close_notify` alert and waits for the peer's reply, then
performs a TCP-level half-close on the write side.

This is the correct way to close a TLS connection. It ensures the peer
receives the alert and can distinguish a clean close from a truncation attack.
After this call, `recv?` will eventually return `none`.

If `timeout` is provided, each round-trip while waiting for the peer's
`close_notify` must complete within that duration or the function throws
`"TLS operation timed out"`. The timeout bounds each round-trip individually,
not the whole shutdown, so a peer that keeps trickling bytes can still extend
the total time. Without a timeout, a stalled or malicious peer can cause this
function to block indefinitely.

If the connection is already in a broken state, the TLS session cannot be trusted to produce a valid
`close_notify`, so this falls back to a plain TCP half-close (`shutdown`) instead. If the shutdown
sequence itself fails (including by timeout), the connection is marked broken and the error is
re-thrown.
-/
def tlsShutdown (s : Connection role) (chunkSize : UInt64 := ioChunkSize) (timeout : Option Millisecond.Offset := none) : Async Unit := do
  if ← s.broken.get then
    Async.ofPromise <| s.native.shutdown
    return

  withConnection s do
    let step := do
      match ← s.ssl.toSession.closeNotify with
      | none => return .done ()
      | some want => return .want want

    let shutdown := Async.ofPromise <| s.native.shutdown

    let result ← pumpIO s.native s.ssl.toSession step chunkSize timeout
        "TLS shutdown stalled: WANT_WRITE but output BIO produced no bytes"
        (fun _ => shutdown) shutdown

    match result with
    | .done () => return ()
    | .timedOut => throw <| IO.userError "TLS operation timed out"

/--
Shuts down the write side of the socket at the TCP level only.

**WARNING:** No TLS `close_notify` alert is sent. The peer's `recv?` will throw a
truncation error instead of returning `none` cleanly. Prefer `tlsShutdown` unless
you deliberately want a hard TCP-level close (e.g. after an error path where the
TLS session is already in an inconsistent state).
-/
@[inline]
def shutdown (s : Connection role) : Async Unit :=
  Async.ofPromise <| s.native.shutdown

/--
Gets the remote address of the socket.
-/
@[inline]
def getPeerName (s : Connection role) : IO SocketAddress :=
  s.native.getPeerName

/--
Gets the local address of the socket.
-/
@[inline]
def getSockName (s : Connection role) : IO SocketAddress :=
  s.native.getSockName

/--
Returns the raw X.509 verification result code for this TLS session.
The value `0` means success (`X509_V_OK`). Use `verifyResultString` for a human-readable
description. These codes are OpenSSL-internal values defined in `<openssl/x509_vfy.h>`.

OpenSSL also returns `X509_V_OK` when the peer presented no certificate at all, so a `0` result does
not by itself prove an authenticated peer; confirm a certificate was received when that matters.
-/
@[inline]
def verifyResult (s : Connection role) : IO UInt64 :=
  s.ssl.toSession.verifyResult

/--
Returns the human-readable X.509 verification result string for this TLS session,
equivalent to `X509_verify_cert_error_string` in OpenSSL (e.g. `"ok"` or `"certificate has expired"`).
-/
@[inline]
def verifyResultString (s : Connection role) : IO String :=
  s.ssl.toSession.verifyResultString

/--
Returns the negotiated TLS protocol version string, e.g. `"TLSv1.3"` or `"TLSv1.2"`.

Only authoritative after a successful handshake: before then OpenSSL reports the highest version the
session is configured to offer rather than a negotiated value. `"unknown"` is returned only in the
unexpected case that OpenSSL reports no version at all.
-/
@[inline]
def negotiatedVersion (s : Connection role) : IO String :=
  s.ssl.toSession.negotiatedVersion

/--
Disables the Nagle algorithm for the socket.
-/
@[inline]
def noDelay (s : Connection role) : IO Unit :=
  s.native.noDelay

/--
Enables TCP keep-alive with a specified delay for the socket.
`delay` must be at least 1 second.
-/
@[inline]
def keepAlive (s : Connection role) (enable : Bool) (delay : Std.Time.Second.Offset)
    (_ : delay.val ≥ 1 := by decide) : IO Unit :=
  s.native.keepAlive enable.toInt8 delay.val.toNat.toUInt32

end Connection
end Std.Async.TCP.SSL
end
