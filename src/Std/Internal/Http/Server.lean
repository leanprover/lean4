/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Internal.Http.Server.Connection
public import Std.Internal.Http.Server.ClientConnection

public section

namespace Std
namespace Http
namespace Server

open Std Internal IO Async TCP
open Time

/--
Serve conection
-/
def serve
  (addr : Net.SocketAddress)
  (onRequest : Request Body → Async (Response Body))
  (onReady : Async Unit := pure ())
  (onFailure : Error → Async Unit := fun _ => pure ())
  (config : Config := {})
  (backlog : UInt32 := 128) : Async Unit := do
    let server ← Socket.Server.mk
    server.bind addr
    server.listen backlog

    onReady

    while true do
      let client ← server.accept
      background (prio := .max) <| serveConnection client onRequest onFailure config
