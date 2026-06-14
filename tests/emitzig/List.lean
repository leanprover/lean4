/-! List length smoke test for the Zig runtime. -/

def main : IO Unit := do
  let xs := [1, 2, 3]
  IO.println xs.length
