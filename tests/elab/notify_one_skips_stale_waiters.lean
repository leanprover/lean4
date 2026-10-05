import Std.Sync

/-!
`Notify.notifyOne` must wake a waiting consumer even when a waiter left behind by a `Selectable.one`
that another selector already won is queued before it.
-/

open Std Async

/-- A selector that queues a plain `wait` on `n` and then wins its race right away. -/
def waitThenWin (n : Notify) : Selector Unit where
  tryFn := pure none
  registerFn w := do
    discard <| n.wait
    w.race (pure ()) (fun p => p.resolve (.ok ()))
  unregisterFn := pure ()

#eval show IO Unit from do
  -- The selectors register in random order; the stale waiter is only queued first in some rounds.
  for _ in [0:20] do
    let n ← Notify.new
    let notified ← (Selectable.one #[
      .case n.selector (fun _ => pure false),
      .case (waitThenWin n) (fun _ => n.notifyOne)] : Async Bool).block
    unless notified do
      throw <| IO.userError "notifyOne returned false with a consumer waiting"
