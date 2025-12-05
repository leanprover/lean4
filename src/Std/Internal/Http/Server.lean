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
  The context used for shutting down all connections and the server.
  -/
  context : Std.Context

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
  let context ← Std.Context.new
  let activeConnections ← Std.Mutex.new 0
  let shutdownPromise : IO.Promise Unit ← IO.Promise.new

  return { context, activeConnections, shutdownPromise, config }

/--
Triggers cancellation of all requests and the accept loop in the server. This function should be used
in conjunction with `waitShutdown` to properly coordinate the shutdown sequence.
-/
@[inline]
def shutdown (s : Server) : Async Unit :=
  s.context.cancel .shutdown

/--
Waits for the server to shut down. Blocks until another task or async operation calls the `shutdown` function.
-/
@[inline]
def waitShutdown (s : Server) : Async Unit := do
  Async.ofAsyncTask (s.shutdownPromise.result?.map (Option.map Except.ok · |>.getD (.error "promise dropped at server shutdown task")))

/--
Triggers cancellation of all requests and the accept loop, then waits for the server to fully shut down.
This is a convenience function combining `shutdown` and then `waitShutdown`.
-/
@[inline]
def shutdownAndWait (s : Server) : Async Unit := do
  s.context.cancel .shutdown
  s.waitShutdown

@[inline]
private def frameCancellation (s : Server) (action : Async α) : Async α := do
  s.activeConnections.atomically (modify (· + 1))

  let result ← action

  s.activeConnections.atomically do
    modify (· - 1)

    if (← get) = 0 ∧ (← s.context.isCancelled) then
      s.shutdownPromise.resolve ()

  return result

/--
Start a new HTTP/1.1 server on the given socket address. This function uses `Async` to handle tasks
and TCP connections, and returns a `Server` structure that can be used to cancel the server.
-/
def serve
    (addr : Net.SocketAddress)
    (onRequest : Request Body → ContextAsync (Response Body))
    (config : Config := {}) (backlog : UInt32 := 128) : Async Server := do

  let httpServer ← Server.new config

  let server ← Socket.Server.mk
  server.bind addr
  server.listen backlog

  background do
    frameCancellation httpServer do
      while not (← httpServer.context.isCancelled) do
        let client ← server.accept
        background (frameCancellation httpServer (serveConnection client onRequest config httpServer.context))

  return httpServer

end Std.Http.Server
