/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module
prelude
public import Std.Time
public import Std.Async.Timer
public import Std.Async.Select
public import Std.Internal.SSL
public import Std.Internal.UV.TCP

/-!
Shared types and internal I/O plumbing for `Std.Async.TCP.SSL`: the `Server`/`Connection`/`Client`
types and the low-level helpers (encrypted feed/flush, the handshake loop) used by the
`Connection`, `Server`, and `Client` operation modules.
-/

public section

namespace Std.Async.TCP.SSL

open Std.Internal.SSL
open Std.Internal.UV.TCP
open Std Net Time

/--
Default buffer size for TLS encrypted socket I/O (16 KiB), chosen to match the maximum TLS plaintext
record size (`SSL3_RT_MAX_PLAIN_LENGTH`, RFC 8446 §5.1). A TLS *ciphertext* record can be slightly
larger than this (it adds framing and AEAD expansion overhead), so a single `recv` is not guaranteed
to capture a whole record; the I/O loops feed partial records back into OpenSSL and retry.
-/
def ioChunkSize : UInt64 := 16 * 1024

namespace Internal

/--
Feeds an encrypted chunk into the SSL input BIO.
-/
@[inline]
def feedEncryptedChunk (ssl : Session) (encrypted : ByteArray) : IO Unit := do
  if encrypted.size == 0 then return ()
  discard <| ssl.feedEncrypted encrypted

/--
Drains all pending encrypted bytes from the SSL output BIO and sends them over TCP.
-/
def flushEncrypted (native : Socket) (ssl : Session) : Async Unit := do
  let out ← ssl.drainEncrypted

  if out.size > 0 then
    Async.ofPromise <| native.send #[out]

/--
Builds a selector from a promise-producing event source and the asynchronous continuation that
consumes a winning value. The continuation is started only after this selector wins the race.
-/
def selectorFromWaiter (tryFn : Async (Option β))
    (acquire : IO (IO.Promise (Except IO.Error α))) (cont : α → Async β)
    (cancel : IO Unit) : Selector β where

  tryFn := tryFn

  registerFn waiter := do
    let source ← acquire

    -- A cancelled source drops its promise, so its `result?` resolves to `none`.
    discard <| IO.mapTask (t := source.result?) fun
      | none => return ()
      | some res =>
        let lose := return ()
        let win promise := do
          try
            let value ← IO.ofExcept res
            let task ← (cont value).asTask
            IO.chainTask task (fun result => promise.resolve result)
          catch e =>
            promise.resolve (.error e)
        waiter.race lose win

  unregisterFn := cancel

/--
Creates a `Selector` that resolves with the next bytes received from a raw TCP socket,
or `none` on EOF. Used internally to race socket receives against a timeout.
-/
private def socketRecvSelector (native : Socket) (chunkSize : UInt64) : Selector (Option ByteArray) :=
  selectorFromWaiter
    (pure none)
    native.waitReadable
    (fun _ => Async.ofPromise <| native.recv? chunkSize)
    native.cancelRecv

/--
The result of waiting for encrypted socket input while driving a TLS operation.
-/
inductive EncryptedRecvResult where

  /--
  Encrypted input was received.
  -/
  | data (bytes : ByteArray)

  /--
  The underlying TCP socket reached EOF.
  -/
  | eof

  /--
  The configured per-receive timeout elapsed.
  -/
  | timedOut

/--
Receives one encrypted chunk from the TCP socket, racing against a fresh `timeout` deadline if
present. Timeout and EOF are returned explicitly so callers can apply operation-specific failure
policy without inspecting exception strings.
-/
def recvEncrypted (native : Socket) (chunkSize : UInt64) (timeout : Option Millisecond.Offset) : Async EncryptedRecvResult := do
  match timeout with
  | none =>
    match ← Async.ofPromise <| native.recv? chunkSize with
    | some bytes => return .data bytes
    | none => return .eof
  | some duration =>
    Selectable.one #[
      .case (← Selector.sleep duration) fun _ =>
        return .timedOut,

      .case (socketRecvSelector native chunkSize) fun
        | some bytes => return .data bytes
        | none => return .eof,
    ]

/--
One step produced by a TLS state-machine operation.
-/
inductive PumpStep (α : Type) where

  /--
  The operation completed with a value.
  -/
  | done (value : α)

  /--
  The operation needs the indicated socket I/O before it can continue.
  -/
  | want (io : IOWant)

/--
The result of driving a TLS state-machine operation through all required socket I/O.
-/
inductive PumpResult (α : Type) where

  /--
  The operation completed with a value.
  -/
  | done (value : α)

  /--
  A socket receive timed out before the TLS operation completed.
  -/
  | timedOut

/--
Drives a TLS state-machine operation through its `WANT_READ`/`WANT_WRITE` transitions. Every step
uses the same output flush ordering and detects `WANT_WRITE` steps that produce no output.

`emptyWriteNeedsRead` selects the recovery for a `WANT_WRITE` step that produced no output. With
in-memory BIOs this state is not expected in practice (`SSL_ERROR_WANT_WRITE` requires a failed BIO
write, and a memory output BIO cannot fill up), but should it occur, operations driven by `SSL_read`
can still be unblocked by feeding more peer input, so they pass `true` to wait for input; write-like
operations pass `false` to fail fast with `stallError` instead of blocking forever.

`initial?` lets callers continue from a step they already performed, as required by
`Session.write`'s queued-write protocol.
-/
partial def pumpIO (native : Socket) (ssl : Session) (step : IO (PumpStep α))
    (chunkSize : UInt64) (timeout : Option Millisecond.Offset)
    (stallError : String) (onDone : α → Async β) (onEof : Async β)
    (initial? : Option (PumpStep α) := none) (emptyWriteNeedsRead := false) : Async (PumpResult β) := do

  let current ← match initial? with
    | some current => pure current
    | none => step

  let pending ← ssl.pendingEncrypted
  flushEncrypted native ssl

  let receive : Async (PumpResult β) := do
    match ← recvEncrypted native chunkSize timeout with
    | .data encrypted =>
      feedEncryptedChunk ssl encrypted
      pumpIO native ssl step chunkSize timeout stallError onDone onEof (emptyWriteNeedsRead := emptyWriteNeedsRead)
    | .eof => return .done (← onEof)
    | .timedOut => return .timedOut

  match current with
  | .done value =>
    return .done (← onDone value)
  | .want .write =>
    if pending > 0 then
      pumpIO native ssl step chunkSize timeout stallError onDone onEof (emptyWriteNeedsRead := emptyWriteNeedsRead)
    else if !emptyWriteNeedsRead then
      throw <| IO.userError stallError
    else
      receive
  | .want .read => receive

/--
Runs the TLS handshake loop to completion, interleaving SSL state machine steps
with TCP I/O. If `timeout` is provided, each TCP receive must complete within
that duration or the loop throws `"TLS operation timed out"`.
-/
partial def runHandshake (native : Socket) (ssl : Session) (chunkSize : UInt64) (timeout : Option Millisecond.Offset := none) : Async Unit := do
  let step := do
    match ← ssl.handshake with
    | none => return .done ()
    | some want => return .want want

  let result ← pumpIO native ssl step chunkSize timeout
    "TLS handshake stalled: WANT_WRITE but output BIO produced no bytes"
    pure (throw <| IO.userError "connection closed during TLS handshake")

  match result with
  | .done () => return ()
  | .timedOut => throw <| IO.userError "TLS operation timed out"

end Internal

/-! ## Types -/

/--
Distinguishes server-accepted and client-initiated TLS connections at the type level.
-/
inductive ConnectionRole where

  /--
  A connection accepted by a `Server` (the local peer is the TLS server).
  -/
  | server

  /--
  A connection initiated by a `Client` (the local peer is the TLS client).
  -/
  | client

/--
A role-indexed SSL session. Keeping the role wrapper here prevents client-only operations such as
setting SNI from being applied to server sessions after a connection is constructed.
-/
inductive ConnectionSession : ConnectionRole → Type where

  /--
  A server-side SSL session.
  -/
  | server (ssl : Session.Server) : ConnectionSession .server

  /--
  A client-side SSL session.
  -/
  | client (ssl : Session.Client) : ConnectionSession .client

namespace ConnectionSession

/--
Erases the statically known session role for role-independent TLS operations.
-/
def toSession (ssl : ConnectionSession role) : Session :=
  match ssl with
  | .server ssl => ssl.toSession
  | .client ssl => ssl.toSession

end ConnectionSession

/--
Represents a TLS-enabled TCP server socket. Carries its own server context so
that each accepted connection gets a session configured from the same context.
-/
structure Server where
  ofNative ::
  native : Socket
  serverCtx : Context.Server

/--
Represents a TLS-enabled TCP connection, parameterized by `role` to prevent
mixing server and client connections after construction.
Use `Client` for outgoing connections and `ServerConn` for server-accepted connections.

A `Connection` wraps a single OpenSSL session, which is **not safe for concurrent use**: do not run
two operations on the same `Connection` at once (e.g. a `send` racing a `recv?`, or two concurrent
`recv?`s). If several tasks share one connection, serialize their access. Note that `recvSelector`
drives a `recv?` on a background task, so registering it counts as an in-flight receive.
-/
structure Connection (role : ConnectionRole) where
  ofNative ::
  native : Socket
  ssl : ConnectionSession role
  broken : IO.Ref Bool

/--
An outgoing TLS client connection.
-/
abbrev Client := Connection .client

/--
An incoming TLS connection accepted by a `Server`.
-/
abbrev ServerConn := Connection .server

namespace Internal

/--
Runs an operation only while the TLS connection is healthy and marks the connection broken if the
operation throws. Operations that return a retryable condition should do so as a value and translate
it to an exception only after this wrapper returns.
-/
def withConnection (s : Connection role) (action : Async α) : Async α := do
  if ← s.broken.get then
    throw <| IO.userError "TLS connection is in a broken state"

  try
    action
  catch e =>
    s.broken.set true
    throw e

end Internal
end Std.Async.TCP.SSL
end
