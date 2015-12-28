constant r : nat → Prop
constant p : nat → Prop

definition q (a : nat) := p a

lemma rq [intro] : ∀ a, r a → q a :=
sorry

attribute q [reducible]

example (a : nat) : r a → p a :=
by blast
