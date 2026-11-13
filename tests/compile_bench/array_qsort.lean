module

import Init.Data.Array.QSort

/-!
Benchmarks `Array.qsort` on inputs with repeated values (#8087).
-/

def time (name : String) (xs : Array Nat) : IO Unit := do
  let size := xs.size
  let start ← IO.monoNanosNow
  let ys := xs.qsort
  unless ys.size = size do
    throw <| .userError s!"{name}: qsort changed the array size"
  let stop ← IO.monoNanosNow
  IO.println s!"measurement: {name} {(stop - start).toFloat / 1000000000.0} s"

public def main (args : List String) : IO Unit := do
  let n := args[0]!.toNat!
  time "constant" (Array.replicate n 0)
  time "low_cardinality" (Array.ofFn fun i : Fin n => i % 16)
