/-!
Tasks queued during the exit still run, so they do not leak.

Each child returns from `main` while a dedicated task is still running. Once the task manager is
shutting down, that task queues pool tasks that nobody waits for, in a different way per mode. They must
still run and print, and they and what their closures capture (here a 1 MB array) must be freed. A leak
is only reported by LeakSanitizer, i.e. in the sanitize build, where a leaking child prints the report and
exits with a nonzero code.

In `dedicatedDependent`, the dedicated task has a pool dependent from the start, and finishing during the
exit queues it. `task_queued_during_shutdown_leak` covers a plain `IO.asTask`. The children are the
compiled binary, hence `.no_interpret`.
-/

/-- Returns once the task manager is shutting down. -/
def waitForShutdown : IO Unit := do
  -- `IO.checkCanceled` holds for every task once the task manager shuts down.
  while !(← IO.checkCanceled) do
    IO.sleep 10

/-- Sized at runtime, so that the array is allocated rather than compiled to a constant. -/
def mkPayload : IO ByteArray :=
  return ByteArray.mk (Array.replicate (1024 * 1024 + (← IO.monoMsNow) % 2) 7)

/-- Indexes the payload at runtime, so that a closure calling this captures the array. -/
def use (tag : String) (p : ByteArray) : IO Unit := do
  if p.get! ((← IO.monoMsNow) % p.size) != 7 then
    throw <| .userError "unexpected payload"
  IO.println s!"{tag} ran"

def atShutdown (mode : String) : IO Unit := do
  waitForShutdown
  let p ← mkPayload
  match mode with
  | "pure" =>
    -- Not kept alive, so dropping it frees the closure, but not the task itself.
    let t := Task.spawn fun _ => p.foldl (fun acc b => acc + b.toNat) 0
    discard <| IO.hasFinished t
  | "map" =>
    let t ← IO.asTask (use "map: source" p)
    discard <| IO.mapTask (fun _ => use "map: dependent" p) t
  | "syncMap" =>
    let t ← IO.asTask (use "syncMap: source" p)
    discard <| IO.mapTask (sync := true) (fun _ => use "syncMap: dependent" p) t
  | "bind" =>
    let t ← IO.asTask (use "bind: source" p)
    discard <| IO.bindTask t fun _ => IO.asTask (use "bind: continuation" p)
  | "bindNested" =>
    -- The bind finishes on the dedicated thread of its nested task, which queues the dependent.
    let src ← IO.asTask (prio := .dedicated) (IO.sleep 10)
    let b ← IO.bindTask (sync := true) src fun _ =>
      IO.asTask (prio := .dedicated) (use "bindNested: nested" p)
    discard <| IO.mapTask (fun _ => use "bindNested: dependent" p) b
  | "prio" =>
    discard <| IO.asTask (prio := .max) (use "prio: task" p)
  | "promiseResolved" =>
    let promise ← IO.Promise.new (α := Nat)
    discard <| IO.mapTask (fun _ => use "promiseResolved: dependent" p) promise.result?
    promise.resolve 1
  | "promiseDropped" =>
    -- Dropping the promise resolves it, which queues the dependent task.
    let promise ← IO.Promise.new (α := Nat)
    discard <| IO.mapTask (fun _ => use "promiseDropped: dependent" p) promise.result?
  | "waitedQueuesMore" =>
    let t ← IO.asTask do
      discard <| IO.asTask (use "waitedQueuesMore: inner" p)
    discard <| IO.wait t
  | _ => throw <| .userError s!"unknown mode {mode}"

def runChild (mode : String) : IO Unit := do
  let proc ← IO.Process.spawn {
    cmd := (← IO.appPath).toString
    args := #[mode]
    stdout := .piped }
  let start ← IO.monoMsNow
  let mut code := none
  while code.isNone && (← IO.monoMsNow) - start < 15000 do
    code ← proc.tryWait
    if code.isNone then IO.sleep 20
  match code with
  | some c => IO.println s!"{mode}: child exited with code {c}"
  | none =>
    proc.kill
    discard proc.wait
    IO.println s!"{mode}: child still running 15 s after it started"
  IO.print (← proc.stdout.readToEnd)

def main (args : List String) : IO Unit := do
  match args with
  | ["dedicatedDependent"] =>
    let p ← mkPayload
    let t ← IO.asTask (prio := .dedicated) do
      waitForShutdown
      use "dedicatedDependent: source" p
    discard <| IO.mapTask (fun _ => use "dedicatedDependent: dependent" p) t
    IO.println "dedicatedDependent: child returns from main"
  | [mode] =>
    discard <| IO.asTask (prio := .dedicated) (atShutdown mode)
    IO.println s!"{mode}: child returns from main"
  | _ =>
    for mode in ["pure", "map", "syncMap", "bind", "bindNested", "prio", "promiseResolved",
        "promiseDropped", "waitedQueuesMore", "dedicatedDependent"] do
      runChild mode
