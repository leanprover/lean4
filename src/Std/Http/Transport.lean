/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Async.TCP
public import Std.Sync.Channel

public section

/-!
# Transport

This module exposes a `Transport` type class that is used to represent different transport mechanisms
that can be used with an HTTP connection.
-/

namespace Std.Http
open Std Async TCP

set_option linter.all true

/--
Generic HTTP interface that abstracts over different transport mechanisms.
-/
class Transport (α : Type) where
  /--
  Send all data through the client connection.
  -/
  sendAll : α → Array ByteArray → Async Unit

  /--
  Get a selector for receiving up to the given number of bytes. It yields `none` once the peer
  closed its side.
  -/
  recvSelector : α → UInt64 → Selector (Option ByteArray)

  /--
  Close the transport connection, cancelling any write still in flight.
  The default implementation is a no-op; override this for transports that require explicit teardown.
  -/
  close : α → IO Unit := fun _ => pure ()

  /--
  Shut down the write side of the connection: the peer reads end-of-stream after everything already
  written, while this side can still read. Returns `false` when the transport cannot, which is what
  the default implementation does.
  -/
  shutdown : α → Async Bool := fun _ => pure false

instance : Transport Socket.Client where
  sendAll client data := do
    let promise ← client.native.send data
    -- A finished send needs no await, and a pending one is mapped on the thread that completes it
    -- instead of in a task of its own.
    if ← IO.hasFinished promise.result? then
      match promise.result?.get with
      | some (.ok ()) => pure ()
      | some (.error e) => throw e
      | none => throw (IO.userError "the promise linked to the Async was dropped")
    else
      Async.ofAsyncTask <| promise.result?.map (sync := true) fun
        | none => .error (IO.userError "the promise linked to the Async was dropped")
        | some res => res
  recvSelector client expect := client.recvSelector expect
  close client := client.close
  shutdown client := do
    client.shutdown
    return true

namespace Internal

/--
Shared state for a bidirectional mock connection.
-/
private structure Mock.SharedState where
  /--
  Client to server direction.
  -/
  clientToServer : Std.CloseableChannel ByteArray

  /--
  Server to client direction.
  -/
  serverToClient : Std.CloseableChannel ByteArray

/--
One end of a mock connection for testing: `Mock.Client` or `Mock.Server`.
-/
structure Mock.Endpoint where
  private shared : Mock.SharedState
  private isServer : Bool

/--
The client end of a mock connection.
-/
abbrev Mock.Client := Mock.Endpoint

/--
The server end of a mock connection.
-/
abbrev Mock.Server := Mock.Endpoint

/--
Creates the client and server ends of a mock connection.
-/
def Mock.new : BaseIO (Mock.Client × Mock.Server) := do
  let shared : Mock.SharedState := ⟨← Std.CloseableChannel.new, ← Std.CloseableChannel.new⟩
  return (⟨shared, false⟩, ⟨shared, true⟩)

namespace Mock.Endpoint

/--
The channel this end receives from.
-/
def getRecvChan (endpoint : Mock.Endpoint) : Std.CloseableChannel ByteArray :=
  if endpoint.isServer then endpoint.shared.clientToServer else endpoint.shared.serverToClient

/--
The channel this end sends to.
-/
def getSendChan (endpoint : Mock.Endpoint) : Std.CloseableChannel ByteArray :=
  if endpoint.isServer then endpoint.shared.serverToClient else endpoint.shared.clientToServer

/--
Appends to `acc` what `chan` has available without waiting, until `expect` bytes, if given.
-/
private partial def drain (chan : Std.CloseableChannel ByteArray) (expect : Option UInt64)
    (acc : ByteArray) : BaseIO ByteArray := do
  if let some expect := expect then
    if acc.size.toUInt64 ≥ expect then return acc
  match ← chan.tryRecv with
  | none => return acc
  | some chunk => drain chan expect (acc ++ chunk)

/--
Sends a single ByteArray.
-/
def send (endpoint : Mock.Endpoint) (data : ByteArray) : Async Unit := do
  Async.ofAsyncTask
    ((← endpoint.getSendChan.send data) |>.map (Except.mapError (IO.userError ∘ toString)))

/--
Waits for data, then joins what else is available up to `expect` bytes, if given. Returns `none`
once the channel is closed.
-/
def recv? (endpoint : Mock.Endpoint) (expect : Option UInt64 := none) : Async (Option ByteArray) := do
  match ← await (← endpoint.getRecvChan.recv) with
  | none => return none
  | some first => return some (← drain endpoint.getRecvChan expect first)

/--
Joins the data available without waiting, or returns `none` if there is none.
-/
def tryRecv? (endpoint : Mock.Endpoint) : BaseIO (Option ByteArray) := do
  match ← endpoint.getRecvChan.tryRecv with
  | none => return none
  | some first => return some (← drain endpoint.getRecvChan none first)

/--
Closes both directions of the mock connection.
-/
def close (endpoint : Mock.Endpoint) : IO Unit := do
  if !(← endpoint.shared.clientToServer.isClosed) then endpoint.shared.clientToServer.close
  if !(← endpoint.shared.serverToClient.isClosed) then endpoint.shared.serverToClient.close

end Mock.Endpoint

instance : Transport Mock.Endpoint where
  sendAll endpoint data := do
    for chunk in data do
      endpoint.send chunk
  recvSelector endpoint _ := endpoint.getRecvChan.recvSelector
  close endpoint := endpoint.close

end Internal

end Std.Http
