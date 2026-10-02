/-!
Tests that with `LEAN_ABORT_ON_NONLINEAR` set, mutating an array marked by `Array.markLinear` while
it is shared aborts instead of silently copying the array.
-/

def bad (n : Nat) : Nat :=
  let xs := (Array.replicate n 0).markLinear
  let ys := xs.set! 0 1
  ys.size + xs.size

def main : IO Unit :=
  IO.println (bad 5)
