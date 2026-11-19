/-!
Tests that `Vector.markLinear` preserves the semantics of the vector it marks, that the marker
survives the reallocation that `Vector.push` performs when the capacity is exhausted, and that
`Vector.propagateMark` only marks its target when its source is marked. The test runs with
`LEAN_ABORT_ON_NONLINEAR` set, so a marker that was wrongly propagated from an unmarked source
would abort.
-/

def fill (n : Nat) : Vector Nat n := Id.run do
  let mut xs := (Vector.replicate n 0).markLinear
  for i in 0...n do
    xs := xs.set! i i
  return xs

def grow : (n : Nat) → Vector Nat n
  | 0 => (Vector.emptyWithCapacity 1).markLinear
  | n + 1 => (grow n).push n

def double (xs : Vector Nat n) : Vector Nat n := Id.run do
  let mut ys := xs.propagateMark (Vector.replicate n 0)
  for i in 0...n do
    ys := ys.set! i (2 * xs[i]!)
  return ys

def shareUnmarked (n : Nat) : Nat × Vector Nat n × Vector Nat n :=
  let xs := Vector.replicate n 0
  let ys := xs.propagateMark (Vector.replicate n 1)
  let zs := ys.set! 0 2
  (ys[0]! + zs[0]!, ys, zs)

def main : IO Unit := do
  IO.println (repr (fill 5))
  IO.println (repr (grow 5))
  IO.println (grow 5 == fill 5)
  IO.println (repr (double (fill 5)))
  let (n, ys, zs) := shareUnmarked 3
  IO.println n
  IO.println (repr ys)
  IO.println (repr zs)
