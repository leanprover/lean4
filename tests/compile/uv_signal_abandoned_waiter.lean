import Std.Async

/-!
A one-shot `Signal.Waiter` that loses a select keeps listening, but once it is dropped it must stop
listening and restore the signal's default action: the event loop must not keep it alive. A child
copy of this program abandons such a waiter and then sends itself SIGINT; it must die from it.
-/

open Std Async

def child : IO Unit := do
  (do
    let waiter ← Signal.Waiter.mk .sigint false
    let sleep ← Selector.sleep 50
    discard <| Selectable.one #[
      .case waiter.selector (fun _ => pure ()),
      .case sleep (fun _ => pure ())]
    : Async Unit).block
  let pid ← IO.Process.getPID
  discard <| IO.Process.output { cmd := "kill", args := #["-INT", toString pid] }
  IO.sleep 2000
  IO.println "survived SIGINT"

def main (args : List String) : IO Unit := do
  if args == ["child"] then
    child
  else if System.Platform.isWindows then
    IO.println "exit code: 130"
  else
    let proc ← IO.Process.spawn { cmd := (← IO.appPath).toString, args := #["child"] }
    IO.println s!"exit code: {← proc.wait}"
