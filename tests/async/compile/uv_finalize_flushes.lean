import Std.Async.Basic
import Std.Internal.UV

open Std Async Internal.UV Net

/-!
When the program exits, libuv lets writes and shutdowns that are already pending finish, for at most
2 s, before it cancels them. The waits it cancels are settled only after that: the sender also has a
recv pending, whose failure makes it close the socket, which would cancel the send if it came first.
The sender starts a large send and a shutdown and then either returns from `main` or calls
`IO.Process.exit 0`; the receiver, which reads everything, must get every byte and then the end of
the stream. The receiver reads slowly, so that the flush takes about half a second.
`uv_finalize_cancels` covers the peer that never reads.
-/

def size : Nat := 16 * 1024 * 1024

def await (p : IO.Promise (Except IO.Error α)) : IO (Except IO.Error α) := do
  return (← IO.wait p.result?).getD (.error (.userError "dropped"))

def outcome (r : Except IO.Error α) : String :=
  match r with
  | .ok _ => "succeeded"
  | .error e => toString e

def sender (port : UInt16) (exit : Bool) : IO Unit := do
  let client ← TCP.Socket.new
  discard <| AsyncTask.ofPromise (← client.connect (.v4 (.mk (.ofParts 127 0 0 1) port))) |>.block
  let recv ← client.recv? 1024
  let send ← client.send #[ByteArray.mk (Array.replicate size 1)]
  let shutdown ← client.shutdown
  discard <| IO.asTask (prio := .dedicated) do
    discard <| await recv
    client.close
  if exit then
    -- Nothing printed after this is sure to appear: `exit` does not wait for other threads.
    IO.Process.exit 0
  discard <| IO.asTask (prio := .dedicated) do
    IO.println s!"send: {outcome (← await send)}"
    IO.println s!"shutdown: {outcome (← await shutdown)}"

def receive (socket : TCP.Socket) : IO Nat := do
  let mut count := 0
  repeat
    match ← IO.ofExcept (← await (← socket.recv? 65536)) with
    | some bytes =>
      count := count + bytes.size
      -- Slow enough that the flush is still running when the sender's waits are cancelled.
      IO.sleep 2
    | none => break
  return count

def run (how : String) : IO Unit := do
  let server ← TCP.Socket.new
  server.bind <| SocketAddressV4.mk (.ofParts 127 0 0 1) 0
  server.listen 1
  let .v4 addr ← server.getSockName | throw <| .userError "not IPv4"
  let accepted ← server.accept
  let child ← IO.Process.spawn {
    cmd := (← IO.appPath).toString, args := #[how, toString addr.port], stdout := .piped }
  let peer ← IO.ofExcept (← await accepted)
  let count ← receive peer
  let output ← child.stdout.readToEnd
  let code ← child.wait
  IO.println s!"{how}:"
  IO.print output
  IO.println s!"received all {size} bytes: {count == size}, exit code {code}"
  peer.close
  server.close

def main (args : List String) : IO Unit := do
  match args with
  | ["return", port] => sender port.toNat!.toUInt16 false
  | ["exit", port] => sender port.toNat!.toUInt16 true
  | _ =>
    run "return"
    run "exit"
