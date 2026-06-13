module

/-! Smoke test program for Lean C emission linked against the Zig runtime. -/

def main : IO Unit :=
  IO.println "Hello, world!"
