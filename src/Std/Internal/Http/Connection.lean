/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Internal.Http.Data.Request
import Std.Internal.Http.Data.Response
import Std.Internal.Http.Data.Body
import Std.Internal.Http.V11.Machine
import Std.Internal.Async.TCP

open Std Internal IO Async
open Std Http V11
open Std Internal Http Data

namespace Std
namespace Http

structure TcpConnection where
  client : TCP.Socket.Client
  conn : Connection

def justify (s : String) (option : Option α) : Except String α :=
  match option with
  | .some res => .ok res
  | none => .error s

def buildRequest (conn : Connection) : Except String Request := do
  let requestLine := conn.requestLine
  let headers := conn.headers
  -- Build request from parsed data
  .ok {
    method := (← (justify "cannot parse method" <| Method.fromString? =<< String.fromUTF8? conn.requestLine.method)),
    uri := (← (justify "cannot parse uri" <| String.fromUTF8? requestLine.uri)),
    version := (← justify "cannot parse version" <| Version.fromNumber? (requestLine.major.toNat - 48) (requestLine.minor.toNat - 48)),
    headers := headers,
    body := .zero
  }

def processEvents (events : Array Event) (bodyData : ByteArray := ByteArray.emptyWithCapacity 4096) : ByteArray × Bool × Option String :=
  events.foldl (fun (body, ready, error) event =>
    match event with
    | .gotData data => (body ++ data, ready, error)
    | .readyToRespond => (body, true, error)
    | .failed msg => (body, ready, some msg)
    | _ => (body, ready, error)
  ) (bodyData, false, none)

def processRequest (conn : Connection) (handler : Request → Async Response) : Async (Except String Response) := do
  match buildRequest conn with
  | .ok request =>
    let (bodyData, _, _) := processEvents conn.events
    let requestWithBody := { request with body := .bytes bodyData }
    .ok <$> handler requestWithBody
  | .error e => return .error e

partial def receive (x : TcpConnection) (handler : Request → Async Response) : Async Unit := do
  IO.println "receiving message"

  let some message ← await (← x.client.recv? 4096)
    | do
      IO.println "connection closed by client"
      return

  let conn := x.conn.feed message
  let events := conn.getEvents

  let (bodyData, isReady, errorMsg) := processEvents events

  match errorMsg with
  | some err =>
    IO.println s!"Error: {err} {conn.headers}"
    return
  | none =>
    if isReady then
      match ← processRequest conn handler with
      | .ok response =>
        let connWithResponse := conn.answer response
        let (dataToSend, finalConn) := connWithResponse.getDataToSend

        if dataToSend.size > 0 then
          let _ ← x.client.send dataToSend
          return

        -- Check if connection should be kept alive
        if finalConn.shouldClose then
          IO.println "closing connection"
          return
        else
          -- Reset connection for next request
          let newConn := { finalConn with
            state := .needRequestLine,
            requestLine := default,
            headers := Headers.empty,
            events := #[]
          }.clearEvents

          background .default (receive ⟨x.client, newConn⟩ handler)
      | .error e =>
        IO.println s!"failed to build request: {e}"
        return
    else
      -- Continue receiving for incomplete request
      background .default (receive ⟨x.client, conn.clearEvents⟩ handler)

partial def acceptLoop (server : TCP.Socket.Server) (fn : Request → Async Response) : Async Unit := do
  IO.println "accepting"

  let socket ← await (← server.accept)
  IO.println "accepted"

  background .default (receive ⟨socket, {}⟩ fn)

  acceptLoop server fn

def start (address : Net.SocketAddress) (fn : Request → Async Response) : Async Unit := do
  let server ← TCP.Socket.Server.mk
  server.bind address
  server.listen 10

  acceptLoop server fn
