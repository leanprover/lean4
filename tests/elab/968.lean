example (p q r : Prop) : (p ∧ q ∧ r)
                       = (r ∧ p ∧ q) :=
by simp only [and_comm, and_left_comm, and_assoc]

example (p q r : Prop) : ((have x := p; x) ∧ (have x := q; x) ∧ (have x := r; x))
                       = ((have x := r; x) ∧ (have x := p; x) ∧ (have x := q; x)) :=
by simp only [and_comm, and_left_comm, and_assoc]
