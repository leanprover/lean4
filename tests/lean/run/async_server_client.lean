import Std.Internal.Async
import Std.Internal.UV
import Std.Net.Addr

open Std.Internal.IO.Async
open Std.Net

-- Define the Async monad
structure Async (α : Type) where
  run : IO (AsyncTask α)

namespace Async

-- Monad instance for Async
instance : Monad Async where
  pure x := Async.mk (pure (AsyncTask.pure x))
  bind ma f := Async.mk do
    let task ← ma.run
    task.bindIO fun a => (f a).run

-- Await function to simplify AsyncTask handling
def await (task : IO (AsyncTask α)) : Async α :=
  Async.mk task

instance : MonadLift IO Async where
  monadLift io := Async.mk (io >>= (pure ∘ AsyncTask.pure))

--------------------------------------------------------------

/-- Mike is another client. -/
def runMike (client: Tcp.Socket) : Async Unit := do
  let mes ← await (client.recv 1024)
  assert! String.fromUTF8! mes == "hi mike!! :)"
  await (client.send (String.toUTF8 "hello robert!!"))
  await (client.shutdown)

/-- Joe is another client. -/
def runJoe (client: Tcp.Socket) : Async Unit := do
  let mes ← await (client.recv 1024)
  assert! String.fromUTF8! mes == "hi joe! :)"
  await (client.send (String.toUTF8 "hello robert!"))
  await client.shutdown

/-- Robert is the server. -/
def runRobert (server: Tcp.Socket) : Async Unit := do
  let joe ← await server.accept
  let mike ← await server.accept

  await (joe.send (String.toUTF8 "hi joe! :)"))
  let mes ← await (joe.recv 1024)
  assert! String.fromUTF8! mes == "hello robert!"

  await (mike.send (String.toUTF8 "hi mike!! :)"))
  let mes ← await (mike.recv 1024)
  assert! String.fromUTF8! mes == "hello robert!!"

  pure ()

def clientServer : IO Unit := do
  let addr := SocketAddressV4.mk (.ofParts 127 0 0 1) 8080

  let server ← Tcp.Socket.mk
  server.bind addr
  server.listen 128

  assert! (← server.getSockName).port == 8080

  let joe ← Tcp.Socket.mk
  let task ← joe.connect addr
  task.block

  assert! (← joe.getPeerName).port == 8080

  joe.noDelay

  let mike ← Tcp.Socket.mk
  let task ← mike.connect addr
  task.block

  assert! (← mike.getPeerName).port == 8080

  mike.noDelay

  let serverTask ← (runRobert server).run

  discard <| (runJoe joe).run
  discard <| (runMike mike).run
  serverTask.block

#eval clientServer
