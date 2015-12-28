constant r : nat → Prop
constant s : nat → Prop
constant p : nat → Prop

definition q (a : nat) := p a

lemma rq₁ [intro] [priority 20] : ∀ a, r a → q a :=
sorry

lemma rq₂ [intro] [priority 10] : ∀ a, s a → q a :=
sorry

attribute q [reducible]

definition lemma1 (a : nat) : r a → s a → p a :=
by blast

print lemma1

attribute rq₂ [intro] [priority 30]

definition lemma2 (a : nat) : r a → s a → p a :=
by blast

print lemma2
