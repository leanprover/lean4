/-!
Tests that without `LEAN_ABORT_ON_NONLINEAR` set, mutating a scalar array marked by `markLinear`
while it is shared silently copies the array instead of aborting.
-/

def bad (n : Nat) : Nat × ByteArray × ByteArray :=
  let bs := (List.replicate n (0 : UInt8)).toByteArray.markLinear
  let cs := bs.set! 0 1
  (cs.size + bs.size, bs, cs)

def main : IO Unit := do
  let (n, bs, cs) := bad 3
  IO.println n
  IO.println bs.toList
  IO.println cs.toList
