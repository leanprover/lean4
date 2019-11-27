partial def spin : Nat → Bool
| n => spin (n)

@[inline] def C : Nat := 0

def f (b : Nat) :=
if strictOr (C == 0) (spin b) then "hello"
else "world"

def main (xs : List String) : IO Unit :=
IO.println (f 0)
