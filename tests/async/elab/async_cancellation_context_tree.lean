import Std.Sync.CancellationContext

open Std

/-!
Tests a cancellation context tree shaped like an HTTP server's: children that start and end, as
connections do, leave nothing behind in their parent, and cancelling the parent still reaches every
child that is alive, with its own reason kept by children cancelled before.
-/

def check (cond : Bool) (msg : String) : IO Unit :=
  unless cond do throw (IO.userError msg)

#eval show IO Unit from do
  let root ← CancellationContext.new
  let mut idle := #[]
  for _ in [0:200] do
    idle := idle.push (← root.fork)
  for _ in [0:1000] do
    let conn ← root.fork
    let task ← conn.fork
    conn.cancel .cancel
    check (← task.isCancelled) "cancelling a connection did not cancel its child"
  check ((← root.countAliveTokens) == 201)
    s!"ended connections left tokens behind: {← root.countAliveTokens} alive, expected 201"
  for conn in idle[0:100] do
    conn.cancel .deadline
  check ((← root.countAliveTokens) == 101)
    s!"{← root.countAliveTokens} alive after 100 idle connections ended, expected 101"
  root.cancel .shutdown
  check ((← root.countAliveTokens) == 0) "the cancelled root still counts alive tokens"
  for conn in idle[0:100] do
    check ((← conn.getCancellationReason) == some CancellationReason.deadline)
      "the root overwrote the reason of a child cancelled before"
  for conn in idle[100:] do
    check ((← conn.getCancellationReason) == some CancellationReason.shutdown)
      "the root did not cancel a child"
