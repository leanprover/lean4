setoption pp::implicit true.
setoption pp::colors   false.
variable N : Type.

definition T (a : N) (f : _ -> _) (H : f a == a) : f (f _) == f _ :=
SubstP (fun x : N, f (f a) == _) (Refl (f (f _))) H.

print environment 1.
