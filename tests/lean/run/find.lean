open nat

lemma aux : ∃ x : nat, x > 10 :=
exists.intro 15 dec_trivial
