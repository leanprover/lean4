import Std.Internal.Async.Signal
import Std.Internal.Async.Select
import Std.Internal.Async

open Std.Internal.IO.Async

def assertBEq [BEq α] [Repr α] (actual expected : α) : IO Unit := do
  unless actual == expected do
    throw <| IO.userError <|
      s!"expected '{repr expected}', got '{repr actual}'"

def select : Async Signal := do
  let signal1 ← Signal.Waiter.mk Signal.sigint false
  let signal2 ← Signal.Waiter.mk Signal.sighup false
  let signal3 ← Signal.Waiter.mk Signal.sigquit false
  let signal4 ← Signal.Waiter.mk Signal.sigusr1 false

  let t ← Selectable.one #[
    .case (← signal1.selector) (fun _ => pure (Task.pure (.ok Signal.sigint))),
    .case (← signal2.selector) (fun _ => pure (Task.pure (.ok Signal.sighup))),
    .case (← signal3.selector) (fun _ => pure (Task.pure (.ok Signal.sigquit))),
    .case (← signal4.selector) (fun _ => pure (Task.pure (.ok Signal.sigusr1))),
  ]

  IO.println s!"Waiting for a signal"

  let signal ← await t

  IO.println s!"received {repr signal}"
  pure signal

def asyncMain : Async Unit := do
  assertBEq (← select) Signal.sigusr1
  assertBEq (← select) Signal.sighup
  assertBEq (← select) Signal.sigquit
  assertBEq (← select) Signal.sigint

def main : IO Unit :=
  asyncMain.wait
