import Std.Internal.UV

/-!
A program exits while a TCP write that a task issued is still pending, because the peer, another
process, never reads.

On Windows libuv cancels pending writes with `CancelIo`, which only reaches I/O issued by the calling
thread, and keeps the socket open until they finish. The writes here are issued by a worker thread, not
by the one that tears the event loop down at exit, and the peer keeps its socket open, so the teardown
must cancel them itself.

The parent runs a peer and a writer, both the compiled binary, hence `.no_interpret`, and kills the
writer if it has not exited after 15 seconds.
-/

open Std.Internal.UV Std.Net

def lo (port : UInt16) : SocketAddress :=
  .v4 (SocketAddressV4.mk (.ofParts 127 0 0 1) port)

def portOf : SocketAddress → UInt16
  | .v4 a => a.port
  | .v6 a => a.port

def await {α : Type} (what : String) (p : IO.Promise (Except IO.Error α)) : IO α := do
  match p.result?.get with
  | some (.ok a) => pure a
  | some (.error e) => throw e
  | none => throw <| IO.userError s!"{what} promise was dropped"

/-- Accepts one connection, never reads from it, and keeps it open until its standard input closes. -/
def peer : IO Unit := do
  let listener ← TCP.Socket.new
  listener.bind (lo 0)
  listener.listen 1
  IO.println (portOf (← listener.getSockName))
  (← IO.getStdout).flush
  let accepted ← await "accept" (← listener.accept)
  discard <| (← IO.getStdin).getLine
  discard <| accepted.getPeerName

/-- Fills the connection to the peer from a task until a write stays pending, then returns from `main`. -/
def writer (port : UInt16) : IO Unit := do
  let client ← TCP.Socket.new
  await "connect" (← client.connect (lo port))
  let chunk := ByteArray.mk (Array.replicate 65536 (0 : UInt8))
  let payload := Array.replicate 512 chunk
  let filled ← IO.asTask do
    -- How much loopback absorbs differs by platform, so writes are added until one stays queued.
    let mut send ← client.send payload
    for _ in [0:16] do
      IO.sleep 20
      if !(← send.isResolved) then break
      send ← client.send payload
    if ← send.isResolved then
      throw <| IO.userError "every write completed, so the test no longer covers a pending one"
  IO.ofExcept (← IO.wait filled)
  IO.println "writer returns from main"

def main (args : List String) : IO Unit := do
  match args with
  | ["peer"] => peer
  | ["writer", port] => writer port.toNat!.toUInt16
  | _ =>
    let peerProc ← IO.Process.spawn {
      cmd := (← IO.appPath).toString
      args := #["peer"]
      stdin := .piped
      stdout := .piped }
    let port ← peerProc.stdout.getLine
    let writerProc ← IO.Process.spawn {
      cmd := (← IO.appPath).toString
      args := #["writer", port.trimAscii.toString]
      stdout := .piped }
    let start ← IO.monoMsNow
    let mut code := none
    while code.isNone && (← IO.monoMsNow) - start < 15000 do
      code ← writerProc.tryWait
      if code.isNone then IO.sleep 20
    if code.isNone then
      writerProc.kill
      discard writerProc.wait
    IO.print (← writerProc.stdout.readToEnd)
    match code with
    | some c => IO.println s!"writer exited with code {c}"
    | none => IO.println "writer still running 15 s after it started"
    peerProc.kill
    discard peerProc.wait
