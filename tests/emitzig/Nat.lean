/-!
EmitZig test: natural number literals and basic operations.
-/
def main : IO Unit :=
  let n := 42
  let m := n + 1
  IO.println s!"{m}"
