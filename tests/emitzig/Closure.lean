/-!
EmitZig test: closures and higher-order functions.
-/
def applyTwice (f : Nat → Nat) (x : Nat) : Nat :=
  f (f x)

def main : IO Unit :=
  let r := applyTwice (fun y => y + 10) 5
  IO.println s!"{r}"
