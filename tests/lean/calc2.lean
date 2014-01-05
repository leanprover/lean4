

variables a b c d e : Nat.
variable  f : Nat -> Nat.
axiom H1 : f a = a.

theorem T : f (f (f a)) = a
:= calc f (f (f a)) = f (f a) : { H1 }
                ... = f a     : { H1 }
                ... = a       : { H1 }.
