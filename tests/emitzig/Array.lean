/-!
EmitZig test: array literals and indexing.
-/
def main : IO Unit :=
  let arr := #[1, 2, 3]
  IO.println s!"{arr[1]!}"
