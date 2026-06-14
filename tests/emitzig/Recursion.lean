/-!
EmitZig test: recursive functions and tail recursion.
-/
def fact (n : Nat) : Nat :=
  if n = 0 then 1 else n * fact (n - 1)

def main : IO Unit :=
  IO.println s!"{fact 5}"
