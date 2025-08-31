def foo (array : Array Nat) : Nat -> Nat
  | 0 => 0
  | n + 1 =>
    let array := array.filter (!.==5)
    if array.isEmpty then
      0
    else
      let arrayOfLast := #[array.back!]
      foo arrayOfLast n

def main : IO Unit :=
  IO.println ("hi")
