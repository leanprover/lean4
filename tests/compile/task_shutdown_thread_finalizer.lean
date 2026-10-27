/-!
The exit waits for every worker thread to free its thread-local state, and runs the tasks that this
queues.

A task replaces its thread's stdout with a stream that holds a promise, which has a dependent task. The
thread frees that stream after the task has finished. Freeing the promise resolves it, which queues the
dependent. The task manager must still be running tasks at that point, rather than leaking the dependent or
being already gone. Each mode installs the stream on a different kind of thread:

* `dedicated`: a dedicated task, once the task manager is shutting down.
* `pool`: a pool task, once the task manager is shutting down.
* `poolIdle`: a pool task that finishes before `main` returns, so its worker is idle when the exit starts.
* `poolSync`: as `pool`, with a `(sync := true)` dependent. It runs while the thread frees the stream and
  prints through the thread's stdout, which must already be reset rather than refer to the freed stream.

The children are the compiled binary, hence `.no_interpret`.
-/

/-- Returns once the task manager is shutting down. -/
def waitForShutdown : IO Unit := do
  -- `IO.checkCanceled` holds for every task once the task manager shuts down.
  while !(← IO.checkCanceled) do
    IO.sleep 10

def mkStream (promise : IO.Promise Unit) : IO.FS.Stream where
  flush := pure ()
  read _ := pure .empty
  write _ := pure ()
  getLine := pure ""
  putStr _ := pure ()
  -- Never called. Makes the stream keep the promise itself alive: a closure using only the pure
  -- `promise.result?` would capture that task instead, and the promise would be dropped at once.
  isTty := do promise.resolve (); return false

/-- Installs the stream on the current thread. -/
def installStream (mode : String) (sync := false) : IO Unit := do
  let promise ← IO.Promise.new (α := Unit)
  discard <| IO.mapTask (sync := sync) (fun _ => IO.println s!"{mode}: the dependent ran") promise.result?
  discard <| IO.setStdout (mkStream promise)

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
  | ["dedicated"] =>
    discard <| IO.asTask (prio := .dedicated) do
      waitForShutdown
      installStream "dedicated"
    IO.println "dedicated: child returns from main"
  | ["pool"] =>
    discard <| IO.asTask do
      waitForShutdown
      installStream "pool"
    IO.println "pool: child returns from main"
  | ["poolSync"] =>
    discard <| IO.asTask do
      waitForShutdown
      installStream "poolSync" (sync := true)
    IO.println "poolSync: child returns from main"
  | ["poolIdle"] =>
    discard <| IO.wait (← IO.asTask (installStream "poolIdle"))
    IO.println "poolIdle: child returns from main"
  | _ =>
    for mode in ["dedicated", "pool", "poolIdle", "poolSync"] do
      runChild mode
