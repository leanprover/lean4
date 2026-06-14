/-! Task/parallelism smoke test for the Zig runtime. -/

def worker (n : Nat) : Nat :=
  n + 1

def main : IO Unit := do
  let t ← IO.asTask (return worker 4)
  match t.get with
  | Except.ok r => IO.println r
  | Except.error e => IO.println (toString e)
