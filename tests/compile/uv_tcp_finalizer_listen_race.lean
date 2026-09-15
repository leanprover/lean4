import Std.Internal.UV
import Std.Net.Addr

/-!
TCP listeners finalized while connections to them are waiting to be reported. The listen callback
runs without the loop holding a reference to the listener, so it reads `handle->data` concurrently
with the finalizer. The finalizer used to overwrite `data` with its raw struct before taking the loop
lock, so a callback in that window dereferenced the struct as a Lean object.

The window is made wide: one poll reports a readable socket together with pending connections on
several listeners, and the read's `(sync := true)` continuation blocks the loop thread while the
listeners are dropped on other threads. Listen callbacks that come after the read in that batch then
run with the finalizers waiting for the lock.
-/

open Std.Internal.UV Std.Net

def lo (port : UInt16) : SocketAddress :=
  .v4 (SocketAddressV4.mk (.ofParts 127 0 0 1) port)

def portOf : SocketAddress → UInt16
  | .v4 a => a.port
  | .v6 a => a.port

def await! (p : IO.Promise (Except IO.Error α)) : IO α := do
  match p.result?.get with
  | some (.ok a) => pure a
  | some (.error e) => throw e
  | none => throw <| IO.userError "promise dropped"

def listenLo : IO (TCP.Socket × UInt16) := do
  let l ← TCP.Socket.new
  l.bind (lo 0)
  l.listen 16
  return (l, portOf (← l.getSockName))

def client (ports : List UInt16) : IO Unit := do
  let s ← TCP.Socket.new
  await! (← s.connect (lo ports.head!))
  IO.sleep 300
  let mut kept := #[]
  for p in ports.tail! do
    let c ← TCP.Socket.new
    discard <| c.connect (lo p)
    kept := kept.push c
  discard <| s.send #[ByteArray.mk #[1]]
  IO.sleep 2000
  -- Keeps the connections open until the parent has dropped its listeners.
  discard <| pure kept

def main (args : List String) : IO Unit := do
  if args.head? == some "client" then
    client (args.tail!.map (·.toNat!.toUInt16))
    return
  let n := 16
  let (l0, p0) ← listenLo
  let blocked ← IO.Promise.new
  let mut ports := #[p0]
  let mut droppers := #[]
  for _ in [0:n] do
    let (l, p) ← listenLo
    ports := ports.push p
    let ref ← IO.mkRef (some l)
    droppers := droppers.push (← IO.asTask (prio := .dedicated) do
      discard <| IO.wait blocked.result?
      ref.set none)
  let child ← IO.Process.spawn
    { cmd := (← IO.appPath).toString, args := #["client"] ++ ports.map toString }
  let a ← await! (← l0.accept)
  let r ← a.recv? 16
  BaseIO.chainTask (sync := true) r.result? fun _ => do
    blocked.resolve ()
    IO.sleep 500
  -- Keeps the loop from polling while the client connects to the listeners and writes to `a`.
  let timer ← Timer.mk 1 false
  let fired ← timer.next
  BaseIO.chainTask (sync := true) fired.result? fun _ => IO.sleep 500
  for d in droppers do
    discard <| IO.wait d
  discard <| child.wait
  IO.println "ok"
