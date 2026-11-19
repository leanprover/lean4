/-!
Tests that with `LEAN_ABORT_ON_NONLINEAR` set, pushing to a shared scalar array marked by
`markLinear` aborts even when the push has to reallocate. `ByteArray.mk` allocates capacity exactly
equal to the size, so the push below takes the growing path through `lean_sarray_ensure_capacity`.
-/

def bad : Nat :=
  let bs := (ByteArray.mk #[0, 1, 2]).markLinear
  let cs := bs.push 9
  cs.size + bs.size

def main : IO Unit :=
  IO.println bad
