/-! Exception handling smoke test for the Zig runtime. -/

def main : IO Unit := do
  try
    throw <| IO.userError "boom"
  catch _ =>
    IO.println "caught"
