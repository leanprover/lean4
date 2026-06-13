/-!
Smoke test for Zig code emission via `lean -z`.
-/
def main : IO Unit :=
  IO.println "hello"
