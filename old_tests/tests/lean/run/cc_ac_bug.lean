example (a b c : nat) (f : nat → nat → nat) : f (b * c) (c * b * a) = f (c * b) (a * c * b) :=
by ac_refl
