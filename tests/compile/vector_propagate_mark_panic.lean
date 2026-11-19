/-!
Tests that with `LEAN_ABORT_ON_NONLINEAR` set, `Vector.propagateMark` transfers the marker of a
vector marked by `Vector.markLinear` onto its target: mutating the target while it is shared aborts
instead of silently copying it.
-/

def bad (n : Nat) : Nat :=
  let xs := (Vector.replicate n 0).markLinear
  let ys := xs.propagateMark (Vector.replicate n 1)
  let zs := ys.set! 0 2
  ys[0]! + zs[0]! + xs[0]!

def main : IO Unit :=
  IO.println (bad 5)
