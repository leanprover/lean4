unsafe def test (x : Nat) : Option Nat :=
unsafeIO (IO.println x *> pure (x+1))

unsafe def main (xs : List String) : IO Unit :=
IO.println $ test xs.head.toNat
