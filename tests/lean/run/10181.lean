import Lean.CoreM

open Lean Meta Core

def asTask {α} (t : CoreM α) : CoreM (BaseIO Unit × Task (CoreM α)) := do
  let task ← (t.toIO (← read) (← get)).asTask
  return (IO.cancel task, task.map (prio := .max) fun
  | .ok (a, s) => do set s; pure a
  | .error e => throwError m!"Task failed:\n{e}")

def asTask' {α} (t : CoreM α) : CoreM (Task (CoreM α)) := (·.2) <$> asTask t

def f : CoreM Name := do
  let t1 ← asTask' do mkFreshUserName `f
  t1.get
