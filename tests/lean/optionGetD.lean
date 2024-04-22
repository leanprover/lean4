import Lean.Data.HashMap

def test (m : Lean.HashMap Nat Nat) : IO (Nat × Nat) := do
  let start := 1
  let mut i := start
  let mut count := 0
  while i != 0 do
    i := (m.find? i).getD (panic! "key is not in the map")
    count := count + 1
  return (i, count)

#eval test (.ofList [(1,3),(3,2),(2,0)])
