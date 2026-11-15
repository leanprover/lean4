/-!
Eight dedicated tasks, each on its own thread, run at the same time. On 32-bit targets, this needs a
default thread stack size small enough for that many stacks to fit into the address space.
-/

def worker (i : Nat) : IO Nat := do
  IO.sleep 200
  return i

def main : IO Unit := do
  let tasks ← (List.range 8).mapM fun i => IO.asTask (prio := .dedicated) (worker i)
  let mut sum := 0
  for t in tasks do
    sum := sum + (← IO.ofExcept t.get)
  IO.println sum
