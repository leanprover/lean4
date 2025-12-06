import Std.Internal.Async.Signal
import Std.Internal.Async.Select
import Std.Internal.Async

open Std.Internal.IO.Async

def assertBEq [BEq α] [Repr α] (actual expected : α) : IO Unit := do
  unless actual == expected do
    throw <| IO.userError <|
      s!"expected '{repr expected}', got '{repr actual}'"

def select (signal1 signal2 signal3 signal4 : Signal.Waiter) : Async Signal := do

  let t ← Selectable.one #[
    .case (← signal1.selector) (fun _ => pure (Task.pure (.ok Signal.sigint))),
    .case (← signal2.selector) (fun _ => pure (Task.pure (.ok Signal.sighup))),
    .case (← signal3.selector) (fun _ => pure (Task.pure (.ok Signal.sigquit))),
    .case (← signal4.selector) (fun _ => pure (Task.pure (.ok Signal.sigusr1))),
  ]

  let signal ← await t

  IO.println s!"received {repr signal}"
  pure signal

def asyncMain : Async Unit := do
  let signal1 ← Signal.Waiter.mk Signal.sigint true
  let signal2 ← Signal.Waiter.mk Signal.sighup true
  let signal3 ← Signal.Waiter.mk Signal.sigquit true
  let signal4 ← Signal.Waiter.mk Signal.sigusr1 true

  assertBEq (← select signal1 signal2 signal3 signal4) Signal.sigusr1
  assertBEq (← select signal1 signal2 signal3 signal4) Signal.sighup
  assertBEq (← select signal1 signal2 signal3 signal4) Signal.sigquit
  assertBEq (← select signal1 signal2 signal3 signal4) Signal.sigint

def main : IO Unit := do
  IO.println s!"Waiting for a signal"
  IO.FS.Stream.flush (← IO.getStdout)

  asyncMain.wait
