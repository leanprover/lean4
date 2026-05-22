def work : Nat := Id.run do
  let mut acc := 0
  for i in [:10000] do
    acc := acc + i
  return acc

def main : IO Unit := do
  IO.println s!"result: {work}"
