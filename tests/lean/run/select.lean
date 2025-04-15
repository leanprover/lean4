import Std.Internal.Async.Select

open Std Internal IO Async

def test3 : IO (AsyncTask String) := do
  let client ← TCP.Socket.Client.mk
  let addr := Net.SocketAddressV4.mk (.ofParts 127 0 0 1) 8080
  IO.println "connecting"
  let task ← client.connect addr
  task.block
  IO.println "connected"

  let timeout ← Sleep.mk 5000
  Selectable.one #[
    .case (← timeout.selector) fun _ => return AsyncTask.pure "No no",
    .case (← client.readSelector 4096) fun data? => do
      if let some data := data? then
        return AsyncTask.pure <| String.fromUTF8! data
      else
        return AsyncTask.pure "Connection closed"
  ]


def main : IO Unit := do
  let task ← test3
  IO.println (← task.block)
