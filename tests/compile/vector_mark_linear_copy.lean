/-!
Tests that without `LEAN_ABORT_ON_NONLINEAR` set, mutating a vector marked by `Vector.markLinear`
while it is shared silently copies the vector instead of aborting.
-/

def bad (n : Nat) : Nat × Vector Nat n × Vector Nat n :=
  let xs := (Vector.replicate n 0).markLinear
  let ys := xs.set! 0 1
  (ys[0]! + xs[0]!, xs, ys)

def main : IO Unit := do
  let (n, xs, ys) := bad 3
  IO.println n
  IO.println (repr xs)
  IO.println (repr ys)
