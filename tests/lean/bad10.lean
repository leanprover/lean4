set::option pp::implicit true.
set::option pp::colors   false.
variable N : Type.

definition T (a : N) (f : _ -> _) (H : f a == a) : f (f _) == f _ :=
substp (fun x : N, f (f a) == _) (refl (f (f _))) H.

print environment 1.
