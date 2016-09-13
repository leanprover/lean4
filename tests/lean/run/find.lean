open nat

notation `dec_trivial` := of_as_true (by tactic.triv)

lemma aux : ∃ x : nat, x > 10 :=
exists.intro 15 dec_trivial
