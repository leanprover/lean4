definition lemma1 (p : nat → Prop) (q : nat → nat → Prop) : (∃ x y, p x ∧ q x y) → q 0 0 ∧ q 1 1 → (∃ x, p x) :=
by blast

print lemma1
