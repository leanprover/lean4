def longArray (n : Nat := 50000) (xs : Array Char := #[]) : Array Char :=
match n with
| 0 => xs
| n+1 => longArray n (xs.push 'a')

def OverflowFold
  {m : Type -> Type}
  [inst1: Monad m]
  (xs: Array Char) :
  StateT Nat m Nat :=
  xs.foldlM (fun (len : Nat) (s : Char) =>
    match s with
      | 'z' => panic "z"
      | _ => return len + 1) 0

def main : IO Unit :=
  let x := (StateT.run (@OverflowFold Id _ longArray) 0).fst
  IO.println x
