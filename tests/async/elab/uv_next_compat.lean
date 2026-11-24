import Std.Async

open Std Internal.UV

/-!
`Timer.next` and `Signal.next` keep promise types without an error, for code written against them.
The promise resolves when the timer fires, and is dropped, so that `result?` is `none`, when the
timer or signal handler is stopped or when the promise from `nextResult` that it follows fails.
-/

def describe (r : Option α) : String :=
  match r with
  | some _ => "resolved"
  | none => "dropped"

def boom : IO.Error := .userError "boom"

/-- SIGWINCH, whose default action is to ignore it. -/
def sigwinch : Int32 := 28

/--
info: timer fires: resolved
timer stopped: dropped
timer fails: dropped
signal stopped: dropped
signal fails: dropped
-/
#guard_msgs in
#eval show IO Unit from do
  let timer ← Timer.mk 10 false
  IO.println s!"timer fires: {describe (← IO.wait (← timer.next).result?)}"

  let timer ← Timer.mk 60000 false
  let fired ← timer.next
  timer.stop
  IO.println s!"timer stopped: {describe (← IO.wait fired.result?)}"

  let timer ← Timer.mk 60000 false
  let fired ← timer.next
  (← timer.nextResult).resolve (.error boom)
  IO.println s!"timer fails: {describe (← IO.wait fired.result?)}"
  timer.stop

  let signal ← Signal.mk sigwinch false
  let received ← signal.next
  signal.stop
  IO.println s!"signal stopped: {describe (← IO.wait received.result?)}"

  let signal ← Signal.mk sigwinch false
  let received ← signal.next
  (← signal.nextResult).resolve (.error boom)
  IO.println s!"signal fails: {describe (← IO.wait received.result?)}"
  signal.stop
