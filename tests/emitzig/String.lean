/-! String concatenation smoke test for the Zig runtime. -/

def main : IO Unit := do
  let s := "hello" ++ " world"
  IO.println s
