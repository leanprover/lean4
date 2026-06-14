/-! Smoke test for stderr output via the Zig runtime. -/

def main : IO Unit :=
  IO.eprintln "stderr"
