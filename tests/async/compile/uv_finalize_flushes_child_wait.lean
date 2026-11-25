import Std.Async.Basic
import Std.Internal.UV

open Std Async Internal.UV Net

/-!
When `main` returns or `IO.Process.exit` is called, a `Child.wait` on a running child must not fail
before pending writes had their grace period to finish: the task it wakes closes the sender's socket,
which during the flush would cut short the send (#16701). The receiver must get every byte of a
large send.
-/

def size : Nat := 16 * 1024 * 1024

def await (p : IO.Promise (Except IO.Error α)) : IO (Except IO.Error α) := do
  return (← IO.wait p.result?).getD (.error (.userError "dropped"))

def outcome (r : Except IO.Error α) : String :=
  match r with
  | .ok _ => "succeeded"
  | .error e => if e.isCanceled then "canceled" else toString e

def sender (port : UInt16) (exit : Bool) : IO Unit := do
  let client ← TCP.Socket.new
  discard <| AsyncTask.ofPromise (← client.connect (.v4 (.mk (.ofParts 127 0 0 1) port))) |>.block
  -- Without its own stdout, it would keep the parent's read of this process's output from ending.
  let child ← IO.Process.spawn { cmd := "sleep", args := #["5"], stdout := .null }
  let send ← client.send #[ByteArray.mk (Array.replicate size 1)]
  discard <| IO.asTask (prio := .dedicated) do
    let wait ← child.wait.toBaseIO
    client.close
    -- Nothing printed after `IO.Process.exit` is sure to appear: it does not wait for other threads.
    unless exit do
      IO.println s!"wait: {outcome wait}"
      IO.println s!"send: {outcome (← await send)}"
  if exit then
    IO.Process.exit 0

def receive (socket : TCP.Socket) : IO Nat := do
  let mut count := 0
  repeat
    match ← IO.ofExcept (← await (← socket.recv? 65536)) with
    | some bytes =>
      count := count + bytes.size
      -- Slow at first, so that the send is still pending when the sender begins to finish, and then
      -- fast, so that it finishes well within the flush.
      if count < 2 * 1024 * 1024 then
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
