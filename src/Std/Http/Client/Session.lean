/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Http.Client.Connection

public section

/-!
# Session

This module defines `Session`, an HTTP/1.1 client session that manages a single
persistent connection and dispatches sequential request/response exchanges over it.
A background task drives the `Connection` loop; callers interact through a channel.

`Session` is transport-agnostic at the type level: the transport type is consumed at
construction time (`Session.new`) but is not stored in the struct. All pooling and
redirect logic works with plain `Session` values regardless of the underlying socket type.
-/

namespace Std.Http.Client

open Std Async TCP Protocol
open Time

set_option linter.all true

/--
An HTTP client session that sends sequential requests over a persistent connection.
-/
structure Session where

  /--
  Queue of requests sent by callers.
  -/
  requestChannel : Std.CloseableChannel RequestPacket

  /--
  Resolves when the background loop exits.
  -/
  shutdown : IO.Promise Unit

  /--
  Configuration for this session.
  -/
  config : Config

  /--
  Cancellation context driving the background connection loop. Cancelling it aborts any in-flight
  exchange (the loop treats cancellation as a shutdown), which is how `close` interrupts a request
  that is blocked waiting on the socket rather than parked on the request channel.
  -/
  context : CancellationContext

  /--
  Unique identifier assigned by the pool when this session is registered.
  Zero for sessions created outside a pool.
  -/
  id : UInt64 := 0

namespace Session

/--
Queue a request and await its response, together with a completion promise that
resolves when the connection is ready for the next request.

Failures are reported as a typed `Client.Error` so callers (e.g. the pool's retry
policy) can distinguish connection-level failures from application-level ones.
-/
def sendTracked (session : Session) (request : Request Body.Any)
    (timeout? : Option Timeout := none) :
    Async (Except Error (Response Body.Stream × IO.Promise (Except Error Unit))) := do
  let responsePromise ← IO.Promise.new
  let completionPromise ← IO.Promise.new

  let task ← session.requestChannel.send { request, responsePromise, completionPromise, timeout? }

  let .ok _ ← await task
    | return .error (.closed "connection closed before request could be sent")

  match ← await responsePromise.result! with
  | .ok response => return .ok (response, completionPromise)
  | .error e => return .error e

/--
Queue a request and await its response.
Use `sendTracked` to receive failures as a typed `Error` instead of a thrown exception.
-/
def send {β : Type} [Coe β Body.Any] (session : Session) (request : Request β) :
    Async (Response Body.Stream) := do
  let (response, _) ← Error.throwOrPure (← session.sendTracked { request with })
  return response

/--
`true` once the session can no longer accept requests: its request channel was closed, either by
`close` or by the background connection loop shutting down (server EOF, idle timeout, protocol
error). Any subsequent `send` fails immediately.
-/
def isClosed (session : Session) : BaseIO Bool :=
  session.requestChannel.isClosed

/--
Wait for the background loop to exit.
-/
def waitShutdown (session : Session) : Async Unit :=
  let res := session.shutdown.result!.map (sync := true) (fun _ => .ok ())
  .mk <| pure (MaybeTask.ofTask res)

/--
Close the session: cancels the background loop's context (aborting any in-flight exchange) and
closes the request channel so queued and future sends fail promptly.
-/
def close (session : Session) : Async Unit := do
  session.context.cancel .shutdown
  discard <| EIO.toBaseIO session.requestChannel.close

/--
Creates an HTTP client session over the given transport and starts its background loop.
The transport type `t` is used only during construction and is not stored in `Session`.
-/
def new [Transport t] (client : t) (config : Config := {}) : Async Session := do
  let requestChannel ← Std.CloseableChannel.new
  let shutdown ← IO.Promise.new
  let context ← CancellationContext.new

  background do
    try
      Std.Http.Client.Connection.handle client
        ({ config := config.toH1Config } : H1.Machine .sending)
        config context requestChannel
    finally
      discard <| shutdown.resolve ()

  pure { requestChannel, shutdown, config, context }

end Std.Http.Client.Session
