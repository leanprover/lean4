/-!
A task that is still running when `main` returns can wait for a pool task that is queued during the
exit, and the process still exits.

When `main` returns, the exit keeps running tasks until none is running or queued. A pool task queued
during the exit must therefore still run, so a thread waiting for it, directly or through `Task.map`,
`Task.bind`, `IO.waitAny` or `Task.get`, is not blocked forever. The task may be queued by a dedicated
task, by a pool task that then waits for it, or by a dedicated task finishing.

Tasks see `IO.checkCanceled` during the exit, so the tasks here that would otherwise run forever stop.

Each mode starts and waits differently. The parent runs each child, which is the compiled binary, hence
`.no_interpret`, and kills it if it has not exited after a few seconds.
-/

/-- Returns once the task manager is shutting down. -/
def waitForShutdown : IO Unit := do
  -- `IO.checkCanceled` holds for every task once the task manager shuts down.
  while !(← IO.checkCanceled) do
    IO.sleep 10

def sleepUntilCanceled : IO Unit := do
  while !(← IO.checkCanceled) do
    IO.sleep 10

partial def respawnUntilCanceled : IO Unit := do
  IO.sleep 10
  unless ← IO.checkCanceled do
    discard <| IO.asTask respawnUntilCanceled

def startAndWait (mode : String) : IO Unit := do
  match mode with
  | "waitAny" =>
    let t ← IO.asTask (pure 42 : IO Nat)
    discard <| IO.waitAny [t]
  | "get" =>
    -- Depends on a runtime value, so that it is not a closed term spawned during initialization.
    let n ← IO.monoMsNow
    let t := Task.spawn fun _ => n
    discard <| IO.lazyPure fun _ => t.get
  | "map" =>
    let t ← IO.asTask (pure 42 : IO Nat)
    discard <| IO.wait (t.map fun r => r.map (· + 1))
  | "bind" =>
    let t ← IO.asTask (pure 42 : IO Nat)
    discard <| IO.wait (← IO.bindTask t fun r => IO.asTask (IO.ofExcept r))
  | "nested" =>
    let outer ← IO.asTask do
      let inner ← IO.asTask (pure 42 : IO Nat)
      IO.ofExcept (← IO.wait inner)
    discard <| IO.wait outer
  | "prio" =>
    let t ← IO.asTask (prio := .max) (pure 42 : IO Nat)
    discard <| IO.wait t
  | "mapDedicated" =>
    -- The dependent is queued by the dedicated thread that finishes the source.
    let t ← IO.asTask (prio := .dedicated) (IO.sleep 50)
    discard <| IO.wait (← IO.mapTask (fun _ => pure 42) t)
  | "waitAnyRunning" =>
    let never ← IO.asTask sleepUntilCanceled
    let soon ← IO.asTask (prio := .dedicated) (IO.sleep 100)
    discard <| IO.waitAny [never, soon]
  | "forever" =>
    discard <| IO.asTask respawnUntilCanceled
  | "process" =>
    -- `IO.Process.output` reads the child's output on a dedicated task.
    let out ← IO.Process.output { cmd := (← IO.appPath).toString, args := #["echo"] }
    if out.stdout != "echo\n" then throw <| .userError s!"unexpected output {out.stdout}"
  | _ =>
    let t ← IO.asTask (pure 42 : IO Nat)
    discard <| IO.wait t
  IO.println s!"{mode}: the task finished"

def child (mode : String) : IO Unit := do
  let prio := if mode == "pool" then Task.Priority.default else .dedicated
  discard <| IO.asTask (prio := prio) do
    waitForShutdown
    startAndWait mode
  IO.println s!"{mode}: child returns from main"

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
  | ["echo"] => IO.println "echo"
  | [mode] => child mode
  | _ =>
    for mode in ["wait", "waitAny", "get", "map", "bind", "nested", "pool", "prio", "mapDedicated",
        "waitAnyRunning", "forever", "process"] do
      runChild mode
