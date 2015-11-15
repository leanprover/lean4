import data.list
open perm

example (p : Prop) (l : list nat) : ¬ l ~ l → p :=
by blast

example (a : nat) : ¬ a = a → false :=
by blast

example (A : Type) (p : Prop) (a b c : A) : a = b → ¬ b = a → p :=
by blast

example (A : Type) (p : Prop) (a b c : A) : a = b → b ≠ a → p :=
by blast
