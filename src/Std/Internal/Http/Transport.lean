/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Internal.Http.Protocol.H1

public section

/-!
# Transport

This module exposes a `Transport` type class that is used to represent different transport mechanisms
that can be used with a HTTP connection.
-/

namespace Std.Http

open Std Internal IO Async TCP

set_option linter.all true

/--
Generic HTTP client interface that abstracts over different transport mechanisms.
-/
class Transport (α : Type) where
  /--
  Receive data from the client connection, up to the expected size.
  Returns None if the connection is closed or no data is available.
  -/
  recv : α → UInt64 → Async (Option ByteArray)

  /--
  Send all data through the client connection.
  -/
  sendAll : α → Array ByteArray → Async Unit

  /--
  Get a selector for receiving data asynchronously.
  -/
  recvSelector : α → UInt64 → Async (Selector (Option ByteArray))

instance : Transport Socket.Client where
  recv client expect := client.recv? expect
  sendAll client data := client.sendAll data
  recvSelector client expect := client.recvSelector expect

open Internal.IO.Async in

private inductive MockClient.Consumer where
  | normal (promise : IO.Promise (Option ByteArray))
  | select (waiter : Waiter (Option ByteArray))

private def MockClient.Consumer.resolve (c : MockClient.Consumer) (data : Option ByteArray) : BaseIO Bool := do
  match c with
  | .normal promise =>
    promise.resolve data
    return true
  | .select waiter =>
    let lose := return false
    let win promise := do
      promise.resolve (.ok data)
      return true
    waiter.race lose win

private structure MockClient.State where
  /--
  Queue of data to be received by the client.
  -/
  receiveQueue : ByteArray := .empty

  /--
  Consumers that are blocked waiting for data.
  -/
  consumers : Std.Queue MockClient.Consumer := .empty

  /--
  Buffer containing all data sent through this client.
  -/
  sentData : ByteArray := .empty

  /--
  Flag indicating whether the connection is closed.
  -/
  closed : Bool := false

/--
Mock client socket for testing HTTP interactions.
-/
structure Mock.Client where
  private state : Std.Mutex MockClient.State

namespace Mock.Client

/--
Create a new mock client with empty buffers.
-/
def new : BaseIO Mock.Client := do
  let state ← Std.Mutex.new {
    receiveQueue := .empty,
    consumers := .empty,
    sentData := .empty,
    closed := false
  }
  return { state }

/--
Add data to the receive queue for testing and notify any waiting receivers.
-/
def enqueueReceive (client : Mock.Client) (data : ByteArray) : BaseIO Unit := do
  client.state.atomically do
    let st ← get
    if st.closed then
      return ()

    let mut newQueue := st.receiveQueue ++ data
    set { st with receiveQueue := newQueue }

    while true do
      let st ← get
      if let some (consumer, consumers) := st.consumers.dequeue? then
        if st.receiveQueue.size > 0 then
          discard <| consumer.resolve (some st.receiveQueue)
          set { st with
            receiveQueue := .empty,
            consumers
          }
        else
          break
      else
        break

/--
Close the mock connection and notify all waiters.
-/
def close (client : Mock.Client) : BaseIO Unit := do
  client.state.atomically do
    let st ← get
    for consumer in st.consumers.toArray do
      discard <| consumer.resolve none

    set { st with
      closed := true,
      consumers := .empty
    }

/--
Get all data that was sent through this client.
-/
def getSentData (client : Mock.Client) : BaseIO ByteArray :=
  client.state.atomically do
    let st ← get
    return st.sentData

/--
Clear the sent data buffer.
-/
def clearSentData (client : Mock.Client) : BaseIO Unit :=
  client.state.atomically do
    modify fun st => { st with sentData := .empty }

/--
Check if the connection is closed.
-/
def isClosed (client : Mock.Client) : BaseIO Bool :=
  client.state.atomically do
    let st ← get
    return st.closed

/--
Try to receive data immediately without blocking.
-/
private def tryRecv' (size : UInt64) : AtomicT MockClient.State Async (Option ByteArray) := do
  let st ← get
  if st.closed then
    return none

  if st.receiveQueue.isEmpty then
    return none
  else
    let data := st.receiveQueue
    let requested := data.extract 0 size.toNat
    let remainder := data.extract size.toNat data.size
    set { st with receiveQueue := remainder }
    return some requested

/--
Try to receive data immediately without blocking.
-/
def tryRecv (client : Mock.Client) (size : UInt64) : Async (Option ByteArray) :=
  client.state.atomically do
    tryRecv' size

/--
Check if data is ready to be received.
-/
@[inline]
private def recvReady' : AtomicT MockClient.State Async Bool := do
  let st ← get
  return !st.receiveQueue.isEmpty || st.closed

/--
Receive data from the mock client, simulating network behavior.
-/
def recv? (client : Mock.Client) (size : UInt64) : Async (Option ByteArray) := do
  client.state.atomically do
    if let some data ← tryRecv' size then
      return (some data)
    else if (← get).closed then
      return none
    else
      let promise ← IO.Promise.new
      modify fun st => { st with consumers := st.consumers.enqueue (.normal promise) }
      Async.ofTask promise.result!

/--
Send all data through the mock client by appending to the sent data buffer.
-/
def sendAll (client : Mock.Client) (data : Array ByteArray) : Async Unit := do
  let closed ← client.state.atomically do
    let st ← get
    if st.closed then
      return true
    else
      let combinedData := data.foldl ByteArray.append .empty
      set { st with sentData := st.sentData ++ combinedData }

      return false

  if closed then
    throw (.userError "Cannot send on closed connection")

/--
Create a selector for receiving data asynchronously.
-/
def recvSelector (client : Mock.Client) (size : UInt64) : Async (Selector (Option ByteArray)) := do
  return {
    tryFn := do
      client.state.atomically do
        if ← recvReady' then
          let data ← tryRecv' size
          return some data
        else
          return none

    registerFn := fun waiter => do
      let lose := return ()
      let win promise := do
        promise.resolve (.ok none)
      waiter.race lose win

    unregisterFn := do
      client.state.atomically do
        let st ← get
        let consumers ← st.consumers.filterM fun
          | .normal _ => return true
          | .select waiter => return !(← waiter.checkFinished)
        set { st with consumers }
  }

instance : Transport Mock.Client where
  recv := Mock.Client.recv?
  sendAll := Mock.Client.sendAll
  recvSelector := Mock.Client.recvSelector

end Std.Http.Mock.Client
