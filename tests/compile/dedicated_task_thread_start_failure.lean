module
import all Lean.Shell

/-!
A dedicated task whose thread fails to start runs on the task pool instead: when spawned directly,
when mapped over a finished task, and when mapped over a task that finishes later. The thread is made
to fail by requesting an impossibly large stack, after a pool worker has started.
-/

public def main : IO Unit := do
  discard <| IO.wait (← IO.asTask (pure ()))
  let p ← IO.Promise.new
  Lean.Internal.setThreadStackSize ((1 : USize) <<< 60)
  let spawned ← IO.asTask (prio := .dedicated) (pure 1)
  let mapped ← IO.mapTask (prio := .dedicated) (t := Task.pure 2) pure
  let deferred ← IO.mapTask (prio := .dedicated) (t := p.result!) pure
  p.resolve 3
  for t in [spawned, mapped, deferred] do
    IO.println (← IO.ofExcept (← IO.wait t))
