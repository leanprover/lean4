import Std.Internal.UV

open Std.Internal.UV

/-!
A repeating `SIGTERM` handler survives two signals while `main` runs, and after the second resolves
the promise that `main` waits for. Finalization then fails the handler's next pending wait, and the
program exits normally (#16701). The child prints to stderr, which is unbuffered.
-/

def next (sig : Signal) : IO (Except IO.Error Int) := do
  match ← sig.nextResult.toBaseIO with
  -- Also when `main` has already returned and libuv has stopped.
  | .error e => return .error e
  | .ok p => return (← IO.wait p.result?).getD (.error (.userError "dropped"))

def await (p : IO.Promise (Except IO.Error Int)) : IO (Except IO.Error Int) := do
  return (← IO.wait p.result?).getD (.error (.userError "dropped"))

def outcome : Except IO.Error Int → String
  | .ok _ => "received"
  | .error e => if e.isCanceled then "canceled" else toString e

def child : IO Unit := do
  -- SIGTERM
  let sig ← Signal.mk 15 true
  -- Listening before the first signal is sent, which would otherwise terminate the child.
  let first ← sig.nextResult
  let done ← IO.Promise.new
  discard <| IO.asTask (prio := .dedicated) do
    IO.eprintln s!"signal 1: {outcome (← await first)}"
    IO.eprintln s!"signal 2: {outcome (← next sig)}"
    done.resolve ()
    IO.eprintln s!"wait: {outcome (← next sig)}"
  let pid ← IO.Process.getPID
  discard <| IO.Process.spawn {
    cmd := "sh", args := #["-c", s!"sleep 0.3; kill -TERM {pid}; sleep 0.3; kill -TERM {pid}"] }
  discard <| IO.wait done.result?
  IO.eprintln "main returns"

def main (args : List String) : IO Unit := do
  if args == ["child"] then
    child
    return
  -- Signals cannot be sent with `kill` on Windows.
  if System.Platform.isWindows then
    IO.println "signal 1: received\nsignal 2: received\nmain returns\nwait: canceled\nexit code 0"
    return
  let out ← IO.Process.output { cmd := (← IO.appPath).toString, args := #["child"] }
  IO.print out.stderr
  IO.println s!"exit code {out.exitCode}"
