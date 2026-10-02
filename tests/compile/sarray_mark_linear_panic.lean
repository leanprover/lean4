/-!
Tests that with `LEAN_ABORT_ON_NONLINEAR` set, mutating a scalar array marked by `markLinear` while
it is shared aborts instead of silently copying the array.
-/

def bad (n : Nat) : Nat :=
  let bs := (List.replicate n (0 : UInt8)).toByteArray.markLinear
  let cs := bs.set! 0 1
  cs.size + bs.size

def main : IO Unit :=
  IO.println (bad 5)
