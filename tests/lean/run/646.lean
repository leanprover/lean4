def build (n : Nat) : Array Unit := do
  let mut out := #[]
  for _ in [0:n] do
    out := out.push ()
  out

@[noinline] def size : IO Nat := pure 50000

def bench (f : ∀ {α : Type}, α → IO Unit := fun _ => ()) : IO Unit := do
  let n ← size
  let arr := build n
  timeit "time" $
    for _ in [:1000] do
      f $ #[1, 2, 3, 4].map fun ty => arr[ty]

#eval bench
