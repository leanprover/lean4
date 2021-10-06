def main (args : List String) : IO Unit := do
  -- create object that outlives thread
  let a ← Task.spawn (prio := Task.Priority.dedicated) (fun _ => [args]) |>.get
  -- free `a`, exporting it back to its original heap
  let t2 ← IO.asTask (prio := Task.Priority.dedicated) (do IO.println a)
  IO.sleep 2500
  -- meanwhile, start new task that takes over `a`'s orphaned segment
  let t3 ← IO.asTask (prio := Task.Priority.dedicated) (IO.println args)
  IO.println "done"
