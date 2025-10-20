/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Internal.Async
public import Std.Internal.Async.TCP
public import Std.Sync.CancellationToken
public import Std.Internal.Http.Server.Config
public import Std.Internal.Http.Server.Connection

public section

/-!
# HTTP Server

This module defines a simple, asynchronous HTTP/1.1 server implementation.

It provides the `Std.Http.Server` structure, which encapsulates all server state, and functions for
starting, managing, and gracefully shutting down the server.

The server runs entirely using `Async` and uses a shared `CancellationToken` to signal shutdowns.
Each active client connection is tracked, and the server automatically resolves its shutdown
promise once all connections have closed.
-/

namespace Std.Http

open Std.Internal.IO.Async TCP

set_option linter.all true

/--
The `Server` structure holds all state required to manage the lifecycle of an HTTP server, including
connection tracking and shutdown coordination.
-/
structure Server where

  /--
  The cancellation token used for shutting down all connections and the server.
  -/
  cancellation : Std.CancellationToken

  /--
  Active HTTP connections
  -/
  activeConnections : Std.Mutex UInt64

  /--
  Indicates when the server has successfully shutdown
  -/
  shutdownPromise : IO.Promise Unit

  /--
  Configuration of the server
  -/
  config : Std.Http.Config

namespace Server

/--
Create a new `Server` structure with an optional configuration.
-/
def new (config : Std.Http.Config := {}) : IO Server := do
  let cancellation ← Std.CancellationToken.new
  let activeConnections ← Std.Mutex.new 0
  let shutdownPromise : IO.Promise Unit ← IO.Promise.new

  return { cancellation, activeConnections, shutdownPromise, config }

/--
Triggers the cancellation of all the requests and the accept loop in the server.
-/
@[inline]
def shutdown (s : Server) : Async Unit :=
  s.cancellation.cancel

/--
Waits for the server to shutdown.
-/
@[inline]
def waitShutdown (s : Server) : Async Unit := do
  Async.ofAsyncTask (s.shutdownPromise.result?.map (Option.map Except.ok · |>.getD (.error "promise dropped at server shutdown task")))

/--
Triggers the cancellation of all the requests and the accept loop in the server and wait for the server
to be cancelled.
-/
@[inline]
def shutdownAndWait (s : Server) : Async Unit := do
  s.cancellation.cancel
  s.waitShutdown

@[inline]
private def frameCancellation (s : Server) (action : Async α) : Async α := do
  s.activeConnections.atomically (modify (· + 1))

  let result ← action

  s.activeConnections.atomically do
    modify (· - 1)

    if (← get) = 0 ∧ (← s.cancellation.isCancelled) then
      s.shutdownPromise.resolve ()

  return result

/--
Start a new HTTP/1.1 server on the given socket address. This function uses the `Async` for handling
tasks and TCP connections, it also returns a `Server` structure that can be used to the cancellation
of the server.
-/
def serve
    (addr : Net.SocketAddress)
    (onRequest : Request Body → Async (Response Body))
    (config : Config := {}) (backlog : UInt32 := 128) : Async Server := do

  let httpServer ← Server.new config

  let server ← Socket.Server.mk
  server.bind addr
  server.listen backlog

  background do
    frameCancellation httpServer do
      while not (← httpServer.cancellation.isCancelled) do
        let client ← server.accept
        background (frameCancellation httpServer (serveConnection client onRequest config) )

  return httpServer

end Std.Http.Server
