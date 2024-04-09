example (p q r : Prop) : (p ∧ q ∧ r)
                       = (r ∧ p ∧ q) :=
by simp only [and_comm, and_left_comm, and_assoc]

example (p q r : Prop) : ((let_fun x := p; x) ∧ (let_fun x := q; x) ∧ (let_fun x := r; x))
                       = ((let_fun x := r; x) ∧ (let_fun x := p; x) ∧ (let_fun x := q; x)) :=
by simp only [and_comm, and_left_comm, and_assoc]
