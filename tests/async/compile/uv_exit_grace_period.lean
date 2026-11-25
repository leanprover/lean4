import Std.Internal.UV

open Std.Internal.UV Std.Net

/-!
`IO.Process.exit` gives pending socket writes `gracePeriodMs` milliseconds to finish. A child exits
while a send to the parent, which never reads, is pending, so the flush runs until the grace period
ends: at once for `0`, and for at least 1.5 s for `1500`.
-/

def size : Nat := 64 * 1024 * 1024

def await (p : IO.Promise (Except IO.Error α)) : IO (Except IO.Error α) := do
  return (← IO.wait p.result?).getD (.error (.userError "dropped"))

def child (port : UInt16) (gracePeriodMs : UInt32) : IO Unit := do
  let client ← TCP.Socket.new
  discard <| IO.ofExcept (← await (← client.connect (.v4 (.mk (.ofParts 127 0 0 1) port))))
  discard <| client.send #[ByteArray.mk (Array.replicate size 1)]
  IO.println "sending"
  (← IO.getStdout).flush
  IO.Process.exit 7 gracePeriodMs

/-- Returns how long the child took to exit after it started sending, and its exit code. -/
def run (server : TCP.Socket) (port : UInt16) (gracePeriodMs : UInt32) : IO (Nat × UInt32) := do
  let accepted ← server.accept
  let proc ← IO.Process.spawn {
    cmd := (← IO.appPath).toString, args := #[toString port, toString gracePeriodMs],
    stdout := .piped }
  let peer ← IO.ofExcept (← await accepted)
  discard <| proc.stdout.getLine
  let start ← IO.monoMsNow
  let mut code := none
  while code.isNone do
    code ← proc.tryWait
    if (← IO.monoMsNow) - start > 10000 then
      proc.kill
      throw <| .userError s!"grace {gracePeriodMs}: no exit within 10 s"
    IO.sleep 10
  let elapsed := (← IO.monoMsNow) - start
  peer.close
  return (elapsed, code.get!)

def main (args : List String) : IO Unit := do
  if let [port, gracePeriodMs] := args then
    child port.toNat!.toUInt16 gracePeriodMs.toNat!.toUInt32
    return
  let server ← TCP.Socket.new
  server.bind <| SocketAddressV4.mk (.ofParts 127 0 0 1) 0
  server.listen 1
  let .v4 addr ← server.getSockName | throw <| .userError "not IPv4"
  let (elapsed, code) ← run server addr.port 0
  IO.println s!"grace 0: exited within 1 s: {decide (elapsed < 1000)}, exit code {code}"
  let (elapsed, code) ← run server addr.port 1500
  IO.println s!"grace 1500: waited at least 1.5 s: {decide (elapsed ≥ 1500)}, exited within 3 s: {decide (elapsed < 3000)}, exit code {code}"
  server.close
