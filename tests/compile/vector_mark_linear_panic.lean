/-!
Tests that with `LEAN_ABORT_ON_NONLINEAR` set, mutating a vector marked by `Vector.markLinear`
while it is shared aborts instead of silently copying the vector.
-/

def bad (n : Nat) : Nat :=
  let xs := (Vector.replicate n 0).markLinear
  let ys := xs.set! 0 1
  ys[0]! + xs[0]!

def main : IO Unit :=
  IO.println (bad 5)
