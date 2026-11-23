/-!
Tests that `Array.markLinear` preserves the semantics of the array it marks and that the marker
survives the reallocation that `Array.push` performs when the capacity is exhausted.
-/

def fill (n : Nat) : Array Nat := Id.run do
  let mut xs := (Array.replicate n 0).markLinear
  for i in 0...n do
    xs := xs.set! i i
  return xs

def grow (n : Nat) : Array Nat := Id.run do
  let mut xs := (Array.emptyWithCapacity 1).markLinear
  for i in 0...n do
    xs := xs.push i
  return xs

def main : IO Unit := do
  IO.println (fill 5)
  IO.println (grow 5)
  IO.println (grow 5 == fill 5)
