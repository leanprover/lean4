/-!
Tests that without `LEAN_ABORT_ON_NONLINEAR` set, mutating an array marked by `Array.markLinear`
while it is shared silently copies the array instead of aborting.
-/

def bad (n : Nat) : Nat × Array Nat × Array Nat :=
  let xs := (Array.replicate n 0).markLinear
  let ys := xs.set! 0 1
  (ys.size + xs.size, xs, ys)

def main : IO Unit := do
  let (n, xs, ys) := bad 3
  IO.println n
  IO.println xs
  IO.println ys
