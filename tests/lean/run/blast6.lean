set_option blast.strategy "preprocess"

lemma lemma1 (bv : nat → Type) (n m : nat) (H : n = m) (b1 : bv n) (b2 : bv m) (H2 : eq.rec_on H b1 = b2) : b1 = eq.rec_on (eq.symm H) b2 :=
by blast

reveal lemma1
print lemma1
