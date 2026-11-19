import Std.Async.Signal
import Std.Async.Select
import Std.Async

open Std.Async

def assertBEq [BEq α] [Repr α] (actual expected : α) : IO Unit := do
  unless actual == expected do
    throw <| IO.userError <|
      s!"expected '{repr expected}', got '{repr actual}'"

def select (signal1 signal2 signal3 signal4 : Signal.Waiter) : Async Signal := do
  IO.println s!"Waiting for a signal"
  IO.FS.Stream.flush (← IO.getStdout)

  let t ← Selectable.one #[
    .case signal1.selector (fun _ => pure (Task.pure Signal.sigint)),
    .case signal2.selector (fun _ => pure (Task.pure Signal.sighup)),
    .case signal3.selector (fun _ => pure (Task.pure Signal.sigquit)),
    .case signal4.selector (fun _ => pure (Task.pure Signal.sigusr1)),
  ]

  let signal ← await t

  IO.eprintln s!"Received {repr signal}"
  pure signal

def asyncMain : Async Unit := do
  let signal1 ← Signal.Waiter.mk Signal.sigint true
  let signal2 ← Signal.Waiter.mk Signal.sighup true
  let signal3 ← Signal.Waiter.mk Signal.sigquit true
  let signal4 ← Signal.Waiter.mk Signal.sigusr1 true

  let _ ← signal1.wait
  let _ ← signal2.wait
  let _ ← signal3.wait
  let _ ← signal4.wait

  assertBEq (← select signal1 signal2 signal3 signal4) Signal.sigusr1
  assertBEq (← select signal1 signal2 signal3 signal4) Signal.sighup
  assertBEq (← select signal1 signal2 signal3 signal4) Signal.sigquit
  assertBEq (← select signal1 signal2 signal3 signal4) Signal.sigint

def main : IO Unit := do
  asyncMain.wait
