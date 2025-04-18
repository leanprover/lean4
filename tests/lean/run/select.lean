import Std.Internal.Async.Timer
import Std.Internal.Async.TCP

open Std Internal IO Async

def test1 : IO (AsyncTask Nat) := do
  let s1 ← Sleep.mk 100
  let s2 ← Sleep.mk 200
  Selectable.one #[
    .case (← s2.selector) fun _ => return AsyncTask.pure 2,
    .case (← s1.selector) fun _ => return AsyncTask.pure 1,
  ]

/-- info: 1 -/
#guard_msgs in
#eval show IO _ from do
  let task ← test1
  IO.ofExcept task.get

def test2 : IO (AsyncTask Nat) := do
  Selectable.one #[
    .case (← Selector.sleep 10) fun _ => return AsyncTask.pure 1,
    .case (← Selector.sleep 10) fun _ => return AsyncTask.pure 2,
    .case (← Selector.sleep 10) fun _ => return AsyncTask.pure 3,
    .case (← Selector.sleep 10) fun _ => return AsyncTask.pure 4,
    .case (← Selector.sleep 10) fun _ => return AsyncTask.pure 5,
  ]

/-- info: true -/
#guard_msgs in
#eval show IO _ from do
  let r1 ← IO.ofExcept (← test2).get
  let r2 ← IO.ofExcept (← test2).get
  let r3 ← IO.ofExcept (← test2).get
  let r4 ← IO.ofExcept (← test2).get
  let r5 ← IO.ofExcept (← test2).get
  let r6 ← IO.ofExcept (← test2).get
  let r7 ← IO.ofExcept (← test2).get
  let r8 ← IO.ofExcept (← test2).get
  let r9 ← IO.ofExcept (← test2).get
  let r10 ← IO.ofExcept (← test2).get
  -- might fail once in 10 million
  return #[r2, r3, r4, r5, r6, r7, r8, r9, r10].any (· != r1)

def test3Client (addr : Net.SocketAddress) : IO (AsyncTask String) := do
  let client ← TCP.Socket.Client.mk
  (← client.connect addr).bindIO fun _ => do
    Selectable.one #[
      .case (← Selector.sleep 1000) fun _ => return AsyncTask.pure "Timeout",
      .case (← client.recvSelector 4096) fun data? => do
        if let some data := data? then
          return AsyncTask.pure <| String.fromUTF8! data
        else
          return AsyncTask.pure "Closed"
    ]

def test3 (serverFn : TCP.Socket.Server → IO (AsyncTask Unit)) (addr : Net.SocketAddress) :
    IO Unit := do
  let server ← TCP.Socket.Server.mk
  server.bind addr
  server.listen 1
  let serverTask ← serverFn server
  let clientTask ← test3Client addr
  serverTask.block
  IO.println (← clientTask.block)

def test3ServerSend (server : TCP.Socket.Server) : IO (AsyncTask Unit) := do
  (← server.accept).bindIO fun client => do
    client.send (String.toUTF8 "Success")

def test3ServerTimeout (server : TCP.Socket.Server) : IO (AsyncTask Unit) := do
  (← server.accept).bindIO fun client => do
    (← Async.sleep 1500).bindIO fun _ => do
      client.shutdown

def test3ServerClose (server : TCP.Socket.Server) : IO (AsyncTask Unit) := do
  (← server.accept).bindIO fun client => client.shutdown

/-- info: Success -/
#guard_msgs in
#eval test3 test3ServerSend (Net.SocketAddressV4.mk (.ofParts 127 0 0 1) 7070)

/-- info: Closed -/
#guard_msgs in
#eval test3 test3ServerClose (Net.SocketAddressV4.mk (.ofParts 127 0 0 1) 7071)

/-- info: Timeout -/
#guard_msgs in
#eval test3 test3ServerTimeout (Net.SocketAddressV4.mk (.ofParts 127 0 0 1) 7072)
