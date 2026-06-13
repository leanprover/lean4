module

/-! EmitZig smoke test covering a minimal `IO.println` program. -/

def main : IO Unit :=
  IO.println "Hello from EmitZig!"
