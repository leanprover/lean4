@[noinline] def f (a : Array Nat) : Nat :=
  Array.casesOn (motive := fun _ => Nat) a (fun data => data.length)

@[noinline] def g (a : Array Nat) : List Nat :=
  a.toList

@[noinline] def h (a : List Nat) : List Nat :=
  g (Array.mk a)

def main : IO Unit := do
  IO.println (f #[2, 3, 4])
  IO.println (g #[2, 3, 4])
  IO.println (h [2, 3, 4])
