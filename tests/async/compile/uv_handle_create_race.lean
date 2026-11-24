import Std.Internal.UV

open Std.Internal.UV

/-!
Creating a libuv handle while the program finishes must not crash it. When `main` returns or
`IO.Process.exit` is called, `lean_uv_stop` walks every handle on the event loop and reads its `data`
field as the Lean object that owns the handle, so `Timer.mk`, `Signal.mk`, `TCP.Socket.new` and
`UDP.Socket.new` must set `data` before they release the loop lock.

The child creates handles of one kind on a dedicated thread, until libuv has stopped and creating
one fails, while the program finishes after 2 ms. The window is a few instructions wide, so where
`taskset` exists (Linux) the parent pins the child to one CPU, on which the creating thread is often
preempted inside it. The parent runs every case up to 40 times there, and 10 times elsewhere, and
stops at its first failure.
-/

/-- The handle constructors. -/
def kinds : List (String × IO Unit) := [
  ("timer", discard <| Timer.mk 1000 false),
  -- SIGWINCH
  ("signal", discard <| Signal.mk 28 false),
  ("tcp", discard TCP.Socket.new),
  ("udp", discard UDP.Socket.new)]

/-- Creates handles until libuv has stopped, after which creating one fails. -/
partial def createUntilStopped (mk : IO Unit) : BaseIO Unit := do
  if let .ok () ← mk.toBaseIO then
    createUntilStopped mk

def child (kind how : String) : IO Unit := do
  let some mk := kinds.lookup kind | throw <| .userError s!"unknown handle kind '{kind}'"
  discard <| IO.asTask (prio := .dedicated) (createUntilStopped mk)
  IO.sleep 2
  if how == "exit" then
    IO.Process.exit 0

/-- `taskset -c 0`, which pins a command to one CPU, if it works here, and nothing otherwise. -/
def pinning (self : String) : IO (Array String) := do
  let probe := IO.Process.output { cmd := "taskset", args := #["-c", "0", self, "probe"] }
  match ← probe.toBaseIO with
  | .ok out => return if out.exitCode == 0 then #["taskset", "-c", "0"] else #[]
  | .error _ => return #[]

/-- Without pinning the race is rarely hit, so fewer runs are spent on it. -/
def runs (pinned : Bool) : Nat := if pinned then 40 else 10

def main (args : List String) : IO Unit := do
  match args with
  | ["probe"] => return
  | ["child", kind, how] => child kind how
  | _ =>
    let self := (← IO.appPath).toString
    let pin ← pinning self
    let n := runs !pin.isEmpty
    let mut ok := true
    for how in ["return", "exit"] do
      for (kind, _) in kinds do
        let argv := pin ++ #[self, "child", kind, how]
        for run in [1:n+1] do
          let out ← IO.Process.output { cmd := argv[0]!, args := argv.extract 1 }
          if out.exitCode != 0 then
            ok := false
            let finish := if how == "exit" then "IO.Process.exit" else "main returning"
            IO.println s!"{kind} created during {finish}: run {run} of {n} ended with exit code \
              {out.exitCode}{if pin.isEmpty then " (not pinned)" else ""}"
            break
    if ok then
      IO.println "ok"

