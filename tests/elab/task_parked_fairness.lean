/-!
Tests that a worker running a chain of dependent tasks, which the task manager keeps on that worker,
still lets independently queued tasks run. With a single worker thread, a task queued while the chain
is running must be picked up after a bounded number of links rather than after the whole chain.
-/

def script := "
def main : IO Unit := do
  let p ← IO.Promise.new (α := Nat)
  let progress ← IO.mkRef 0
  let flag ← IO.mkRef false
  let seen ← IO.mkRef (none : Option Nat)
  let mut t : Task Nat := p.resultD 0
  for _ in [0:20000] do
    t ← BaseIO.mapTask (t := t) fun k => do
      progress.set k
      if (← flag.get) && (← seen.get).isNone then
        seen.set (some k)
      return k + 1
  p.resolve 0
  let before ← progress.get
  -- queued from outside the pool while the only worker runs the chain
  let _ ← IO.asTask (flag.set true)
  let _ ← IO.wait t
  match ← seen.get with
  | none => IO.println \"queued task never ran\"
  | some k =>
    if k - before < 100 then
      IO.println \"queued task ran within bound\"
    else
      IO.println s!\"queued task ran only at link {k}, chain was at {before} when it was queued\"
"

def test : IO String := do
  IO.FS.withTempFile fun h path => do
    h.putStr script
    h.flush
    -- `-j1`: a single pool worker, so nothing else could run the queued task
    let out ← IO.Process.output {
      cmd := (← IO.appPath).toString
      args := #["-j1", "--run", path.toString]
    }
    unless out.exitCode == 0 do
      throw <| .userError s!"child failed: {out.stdout}{out.stderr}"
    return out.stdout.trimAsciiEnd.copy

/-- info: "queued task ran within bound" -/
#guard_msgs in #eval test
