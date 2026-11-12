/-!
Dropping the last reference to a `Task.bind` task while the bound function runs, when the function
then returns an unfinished task, must release that task. It used to leak, together with its
closure. Here the returned task's closure holds the only reference to `witness`, so `witness`
being dropped, which resolves `witness.result?` to `none`, shows that the task was released.
-/

def waitFor (what : String) (cond : IO Bool) : IO Unit := do
  for _ in [0:1000] do
    if ← cond then return
    IO.sleep 10
  IO.println s!"timed out waiting for {what}"
  IO.Process.exit 1

def main : IO Unit := do
  let go : IO.Promise Unit ← IO.Promise.new
  let never : IO.Promise Unit ← IO.Promise.new
  let witness : IO.Promise Unit ← IO.Promise.new
  let dropped := witness.result?
  let slot ← IO.mkRef <| some <| (Task.pure ()).bind fun _ =>
    -- Block until the bind task has been dropped, then return a task that does not finish.
    match go.result?.get with
    | some _ => never.result?.map fun _ => witness
    | none => .pure witness
  waitFor "the bound function to start" do
    let some t ← slot.get | return false
    return (← IO.getTaskState t) == .running
  slot.set none
  go.resolve ()
  waitFor "the returned task to be released" (IO.hasFinished dropped)
  IO.println s!"witness dropped: {(← IO.wait dropped).isNone}"
  never.resolve ()
