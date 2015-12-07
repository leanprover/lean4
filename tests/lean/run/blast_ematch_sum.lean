import data.nat
open nat

definition Sum : nat → (nat → nat) → nat :=
sorry

notation `Σ` binders ` < ` n `, ` r:(scoped f, Sum n f) := r

lemma Sum_const [forward] (n : nat) (c : nat) : (Σ x < n, c) = n * c :=
sorry

lemma Sum_add [forward] (f g : nat → nat) (n : nat) : (Σ x < n, f x + g x) = (Σ x < n, f x) + (Σ x < n, g x) :=
sorry

attribute add.assoc add.comm add.left_comm mul_zero zero_mul mul_one add_zero zero_add one_mul mul.comm mul.assoc mul.left_comm [forward]

set_option blast.strategy "ematch"

example (f : nat → nat) (n : nat) : (Σ x < n, f x + 1) = (Σ x < n, f x) + n :=
by blast

example (f g h : nat → nat) (n : nat) : (Σ x < n, f x + g x + h x) = (Σ x < n, h x) + (Σ x < n, f x) + (Σ x < n, g x) :=
by blast

example (f g h : nat → nat) (n : nat) : (Σ x < n, f x + g x + h x) = Sum n h + (Σ x < n, f x) + (Σ x < n, g x) :=
by blast

example (f g h : nat → nat) (n : nat) : (Σ x < n, f x + g x + 0) = (Σ x < n, f x) + (Σ x < n, g x) :=
by blast

example (f g h : nat → nat) (n : nat) : (Σ x < n, f x + g x + h x + 2) = 0 + Sum n h + (Σ x < n, f x) + (Σ x < n, g x) + 2 * n :=
by blast
