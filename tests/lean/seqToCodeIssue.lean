@[noinline] def print (n : Nat) : IO Unit :=
  IO.println n

set_option trace.Compiler.saveMono true
def f (b : Bool) : IO Unit := do
  let a : Nat ← match b with
    | true  => pure 0
    | false => pure 1
  print a
  print a
