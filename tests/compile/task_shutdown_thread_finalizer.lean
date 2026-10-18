/-!
The exit waits for a dedicated task's thread to free its thread-local state, and runs the tasks that this
queues.

Once the task manager is shutting down, a dedicated task replaces its thread's stdout with a stream that
holds a promise, which has a dependent task. The thread frees that stream when it exits, after the task
has finished. Freeing the promise resolves it, which queues the dependent. The task manager must still be
running tasks at that point, rather than leaking the dependent or being already gone. The children are
the compiled binary, hence `.no_interpret`.
-/

/-- Returns once the task manager is shutting down and its idle workers have exited. -/
def waitForShutdown : IO Unit := do
  -- `IO.checkCanceled` holds for every task once the task manager shuts down.
  while !(← IO.checkCanceled) do
    IO.sleep 10
  IO.sleep 100

def mkStream (promise : IO.Promise Unit) : IO.FS.Stream where
  flush := pure ()
  read _ := pure .empty
  write _ := pure ()
  getLine := pure ""
  putStr _ := pure ()
  -- Never called; makes the stream keep the promise alive.
  isTty := do discard <| IO.wait promise.result?; return false

def runChild : IO Unit := do
  let proc ← IO.Process.spawn {
    cmd := (← IO.appPath).toString
    args := #["child"]
    stdout := .piped }
  let start ← IO.monoMsNow
  let mut code := none
  while code.isNone && (← IO.monoMsNow) - start < 15000 do
    code ← proc.tryWait
    if code.isNone then IO.sleep 20
  match code with
  | some c => IO.println s!"child exited with code {c}"
  | none =>
    proc.kill
    discard proc.wait
    IO.println "child still running 15 s after it started"
  IO.print (← proc.stdout.readToEnd)

def main (args : List String) : IO Unit := do
  match args with
  | ["child"] =>
    discard <| IO.asTask (prio := .dedicated) do
      waitForShutdown
      let promise ← IO.Promise.new (α := Unit)
      discard <| IO.mapTask (fun _ => IO.println "the dependent ran") promise.result?
      discard <| IO.setStdout (mkStream promise)
    IO.println "child returns from main"
  | _ => runChild
