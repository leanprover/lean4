constant f {A : Type} (a : A) {B : Type} (b : B) : nat

example (a b c d : nat) : a = c → b = d → f a b = f c d :=
by simp
