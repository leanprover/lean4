import Std.Async

/-!
`ContextAsync.raceAll`, `ContextAsync.race` and `ContextAsync.concurrentlyAll` cancel the child
contexts they fork once they return, and never the caller's own context. `ContextAsync.run` and
`ContextAsync.background` cancel the context they create once the action is done, including when it
throws.
-/

open Std Async

def check (cond : Bool) (msg : String) : IO Unit :=
  unless cond do throw <| IO.userError msg

/-- Runs `op` in a fresh root context and checks its result, that the root is not cancelled, and
that no context forked below the root is still alive. -/
def checkCombinator [BEq α] [ToString α] (name : String) (expected : α) (op : ContextAsync α) :
    IO Unit := do
  let root ← CancellationContext.new
  let (result, cancelled) ← Async.block <| ContextAsync.runIn root do
    return (← op, ← ContextAsync.isCancelled)
  check (result == expected) s!"{name}: unexpected result {result}"
  check (!cancelled) s!"{name} cancelled the caller's context"
  -- Cancellation of the children may complete on another task.
  IO.sleep 100
  let alive := (← root.countAliveTokens) - 1
  check (alive == 0) s!"{name} left {alive} child contexts alive"

#eval checkCombinator "raceAll" 1 <|
  ContextAsync.raceAll #[(pure 1 : ContextAsync Nat), (do Async.sleep 1000; pure 2)]

#eval checkCombinator "race" 1 <|
  ContextAsync.race (pure 1 : ContextAsync Nat) (do Async.sleep 1000; pure 2)

#eval checkCombinator "concurrentlyAll" #[1, 2] <|
  ContextAsync.concurrentlyAll #[(pure 1 : ContextAsync Nat), pure 2]

#eval show IO Unit from do
  let captured ← IO.mkRef (none : Option CancellationContext)
  let result ← (Async.block <| ContextAsync.run do
    captured.set (some (← ContextAsync.getContext))
    (throw (IO.userError "boom") : ContextAsync Unit)).toBaseIO
  check (result matches .error _) "the action was expected to throw"
  let some ctx ← captured.get | throw <| IO.userError "context was not captured"
  check (← ctx.isCancelled) "run did not cancel its context after the action threw"

#eval show IO Unit from do
  let captured ← IO.mkRef (none : Option CancellationContext)
  let cancelled ← Async.block <| ContextAsync.run do
    ContextAsync.background do
      captured.set (some (← ContextAsync.getContext))
      (throw (IO.userError "boom") : ContextAsync Unit)
    Async.sleep 200
    let some ctx ← captured.get | throw <| IO.userError "context was not captured"
    ctx.isCancelled
  check cancelled "background did not cancel its context after the action threw"
