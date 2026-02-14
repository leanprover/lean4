/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Internal.Async
public import Std.Internal.Async.TCP
public import Std.Internal.Async.TCP.SSL
public import Std.Sync.CancellationToken
public import Std.Internal.Http.Server.Config
public import Std.Internal.Http.Server.Handler
public import Std.Internal.Http.Server.Connection

public section

/-!
# HTTP Server

This module defines a simple, asynchronous HTTP/1.1 server implementation.

It provides the `Std.Http.Server` structure, which encapsulates all server state, and functions for
starting, managing, and gracefully shutting down the server.

The server runs entirely using `Async` and uses a shared `CancellationContext` to signal shutdowns.
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
  context : Std.CancellationContext

  /--
  Active HTTP connections
  -/
  activeConnections : Std.Mutex UInt64

  /--
  Indicates when the server has successfully shutdown
  -/
  shutdownPromise : Std.Channel Unit

  /--
  Configuration of the server
  -/
  config : Std.Http.Config

namespace Server

/--
Create a new `Server` structure with an optional configuration.
-/
def new (config : Std.Http.Config := {}) : IO Server := do
  let context ← Std.CancellationContext.new
  let activeConnections ← Std.Mutex.new 0
  let shutdownPromise ← Std.Channel.new

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
  Async.ofAsyncTask ((← s.shutdownPromise.recv).map Except.ok)

/--
Returns a `Selector` that waits for the server to shut down.
-/
@[inline]
def waitShutdownSelector (s : Server) : Selector Unit :=
  s.shutdownPromise.recvSelector

/--
Triggers cancellation of all requests and the accept loop, then waits for the server to fully shut down.
This is a convenience function combining `shutdown` and then `waitShutdown`.
-/
@[inline]
def shutdownAndWait (s : Server) : Async Unit := do
  s.context.cancel .shutdown
  s.waitShutdown

@[inline]
private def frameCancellation (s : Server) (action : ContextAsync α) : ContextAsync α := do
  s.activeConnections.atomically (modify (· + 1))

  let result ← action

  s.activeConnections.atomically do
    modify (· - 1)

    if (← get) = 0 ∧ (← s.context.isCancelled) then
      discard <| s.shutdownPromise.send ()

  return result

/--
Start a new HTTP/1.1 server on the given socket address. This function uses `Async` to handle tasks
and TCP connections, and returns a `Server` structure that can be used to cancel the server.
-/
def serve {σ : Type} [Handler σ]
    (addr : Net.SocketAddress)
    (handler : σ)
    (config : Config := {}) (backlog : UInt32 := 128) : Async Server := do

  let httpServer ← Server.new config

  let server ← Socket.Server.mk
  server.bind addr
  server.listen backlog

  let runServer := do
    frameCancellation httpServer do
      while true do
        let result ← Selectable.one #[
          .case (server.acceptSelector) (fun x => pure <| some x),
          .case (← ContextAsync.doneSelector) (fun _ => pure none)
        ]

        match result with
        | some client =>
          let extensions : Extensions := match (← EIO.toBaseIO client.getPeerName) with
            | .ok addr => Extensions.empty.insert (Server.RemoteAddr.mk addr)
            | .error _ => Extensions.empty

          ContextAsync.background (frameCancellation httpServer (serveConnection client handler config extensions))
        | none => break

  background (runServer httpServer.context)

  return httpServer

/--
Start a new HTTPS (HTTP over TLS) server on the given socket address.
The server context is configured with the provided PEM certificate and key files.
-/
def serveSSL {σ : Type} [Handler σ]
    (addr : Net.SocketAddress)
    (handler : σ)
    (certFile keyFile : String)
    (config : Config := {}) (backlog : UInt32 := 128)
    (chunkSize : UInt64 := TCP.SSL.ioChunkSize) : Async Server := do

  TCP.SSL.Server.configureContext certFile keyFile

  let httpServer ← Server.new config

  let server ← TCP.SSL.Server.mk
  server.bind addr
  server.listen backlog

  let runServer := do
    frameCancellation httpServer do
      while true do
        let result ← Selectable.one #[
          .case (server.acceptSelector) (fun x => pure <| some x),
          .case (← ContextAsync.doneSelector) (fun _ => pure none)
        ]

        match result with
        | some client =>
          let extensions : Extensions := match (← EIO.toBaseIO client.getPeerName) with
            | .ok addr => Extensions.empty.insert (Server.RemoteAddr.mk addr)
            | .error _ => Extensions.empty

          ContextAsync.background (frameCancellation httpServer do
            try
              client.handshake chunkSize
              serveConnection client handler config extensions
            catch _ =>
              pure ())
        | none => break

  background (runServer httpServer.context)

  return httpServer

end Std.Http.Server
