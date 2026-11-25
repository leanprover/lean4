import Std.Internal.UV
import Std.Sync.Mutex

open Std.Internal.UV Std.Net

/-!
`IO.Process.exit` must exit with its code even while a blocked `(sync := true)` continuation keeps
libuv busy (#16701), after a bounded wait for libuv's locks. Each case runs in a child process:

* `loop`: the continuation blocks the event loop thread on a mutex that the exiting thread holds.
* `finalize`: as `loop`, but `main` has returned, and its finalization waits for the loop thread
  while a task that holds the mutex exits.
* `flush`: `main` has returned, and the flush of its finalization runs the continuation of a send to
  the parent, which blocks on a mutex that an exiting task holds.

The parent kills a child that has not exited after 10 s.
-/

def size : Nat := 8 * 1024 * 1024

def await (p : IO.Promise (Except IO.Error α)) : IO (Except IO.Error α) := do
  return (← IO.wait p.result?).getD (.error (.userError "dropped"))

/-- Blocks the event loop thread on `m` from a timer's `(sync := true)` continuation. -/
def blockLoop (m : Std.BaseMutex) : IO Unit := do
  let started ← IO.Promise.new
  let fired ← (← Timer.mk 10 false).nextResult
  discard <| IO.mapTask (sync := true) (t := fired.result?) fun _ => do
    started.resolve ()
    m.lock
  discard <| IO.wait started.result?

/-- Takes `m` on a dedicated thread, which then exits with `code` after 300 ms. -/
def exitHolding (m : Std.BaseMutex) (code : UInt8) : IO Unit := do
  let locked ← IO.Promise.new
  discard <| IO.asTask (prio := .dedicated) do
    m.lock
    locked.resolve ()
    IO.sleep 300
    (IO.Process.exit code : IO Unit)
  discard <| IO.wait locked.result?

def child : List String → IO Unit
  | ["loop"] => do
    let m ← Std.BaseMutex.new
    m.lock
    blockLoop m
    IO.Process.exit 3
  | ["finalize"] => do
    let m ← Std.BaseMutex.new
    exitHolding m 4
    blockLoop m
  | ["flush", port] => do
    let m ← Std.BaseMutex.new
    let client ← TCP.Socket.new
    discard <| IO.ofExcept (← await (← client.connect (.v4 (.mk (.ofParts 127 0 0 1) port.toNat!.toUInt16))))
    let send ← client.send #[ByteArray.mk (Array.replicate size 1)]
    discard <| IO.mapTask (sync := true) (fun _ => m.lock) send.result?
    exitHolding m 5
  | args => throw <| .userError s!"unknown arguments {args}"

/-- Reads until the connection ends, slowly at first so that the send is still pending when the child's
`main` returns. -/
partial def receive (socket : TCP.Socket) (count : Nat := 0) : IO Unit := do
  if let .ok (some bytes) ← await (← socket.recv? 65536) then
    if count < size / 2 then IO.sleep 1
    receive socket (count + bytes.size)

def waitBounded (mode : String) (proc : IO.Process.Child {}) : IO Unit := do
  let start ← IO.monoMsNow
  repeat
    if let some code ← proc.tryWait then
      IO.println s!"{mode}: exit code {code}"
      return
    if (← IO.monoMsNow) - start > 10000 then
      proc.kill
      IO.println s!"{mode}: no exit within 10 s"
      return
    IO.sleep 10

def main (args : List String) : IO Unit := do
  unless args.isEmpty do
    child args
    return
  let self := (← IO.appPath).toString
  let server ← TCP.Socket.new
  server.bind <| SocketAddressV4.mk (.ofParts 127 0 0 1) 0
  server.listen 1
  let .v4 addr ← server.getSockName | throw <| .userError "not IPv4"
  let accepted ← server.accept
  let loop ← IO.Process.spawn { cmd := self, args := #["loop"] }
  let finalize ← IO.Process.spawn { cmd := self, args := #["finalize"] }
  let flush ← IO.Process.spawn { cmd := self, args := #["flush", toString addr.port] }
  let peer ← IO.ofExcept (← await accepted)
  let reader ← IO.asTask (prio := .dedicated) (receive peer)
  waitBounded "loop" loop
  waitBounded "finalize" finalize
  waitBounded "flush" flush
  discard <| IO.wait reader
  peer.close
  server.close
