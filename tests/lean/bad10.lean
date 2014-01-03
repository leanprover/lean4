SetOption pp::implicit true.
SetOption pp::colors   false.
Variable N : Type.

Definition T (a : N) (f : _ -> _) (H : f a == a) : f (f _) == f _ :=
SubstP (fun x : N, f (f a) == _) (Refl (f (f _))) H.

Show Environment 1.
