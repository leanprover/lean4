structure S :=
(n : Nat)
(u : USize)

@[noinline] def f (u : USize) : S :=
{ n := 0, u := u }

def main : IO Unit :=
IO.println (f 2).u
