theorem and_comm (a b : Prop) : (a ∧ b) = (b ∧ a) := sorry

theorem and_assoc (a b c : Prop) : ((a ∧ b) ∧ c) = (a ∧ (b ∧ c)):= sorry

theorem and_left_comm (a b c : Prop) : (a ∧ (b ∧ c)) = (b ∧ (a ∧ c)) := sorry

example (p q r : Prop) : (p ∧ q ∧ r)
                       = (r ∧ p ∧ q) :=
by simp only [and_comm, and_left_comm, and_assoc]

example (p q r : Prop) : ((let_fun x := p; x) ∧ (let_fun x := q; x) ∧ (let_fun x := r; x))
                       = ((let_fun x := r; x) ∧ (let_fun x := p; x) ∧ (let_fun x := q; x)) :=
by simp only [and_comm, and_left_comm, and_assoc]
