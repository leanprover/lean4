

def f (xs : List Nat) : Nat :=
match xs with
| [] => 0
| x::xs =>
  match xs with
  | []  => 0
  -- This examples fails if we write the following alternative as
  -- | _ => f xs + 1
  | xs => f xs + 1

def g (xs : List Nat) : Nat :=
match xs with
| [] => 0
| y::ys =>
  match ys with
  | []       => 0
  | _::_::zs => g zs + 1
  | zs       => g zs + 3
