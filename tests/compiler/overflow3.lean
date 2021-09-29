def longArray (n : Nat := 50000) (xs : Array Char := #[]) : Array Char :=
match n with
| 0 => xs
| n+1 => longArray n (xs.push 'a')

def OverflowLoop
  {m : Type -> Type}
  [inst1: Monad m]
  (xs: Array Char) :
  StateT Nat m Nat := do
  let mut out := 0
  for c in xs do
    match c with
    | 'z' => panic "z"
    | _ => out := out + 1
  return out

def main : IO Unit :=
  let x := (StateT.run (@OverflowLoop Id _ longArray) 0).fst
  IO.println x
