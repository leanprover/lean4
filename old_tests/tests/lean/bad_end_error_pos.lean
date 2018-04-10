example (a b c : nat) (f : nat → nat) : f (a + b + c) = f (b + c + a) :=
by ac_refl

example (a b c : nat) (f : nat → nat) : f (a + b + (c * b * a)) = f (b + (a * c * b) + a) :=
by ac_refl

end

example (a b c : nat) (f : nat → nat → nat) : f (b * c) (c * b * a) = f (c * b) (a * c * b) :=
by ac_refl

example (a b c : nat) (f : nat → nat) : f (a + (b * c) + (c * b * a)) = f ((c * b) + (a * c * b) + a) :=
by ac_refl
