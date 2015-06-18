variable p : nat → Prop
variable q : nat → Prop
variables a b c : nat

example : p c → p b → q b → p a → ∃ x, p x ∧ q x :=
by intros; repeat (constructor | eassumption); now
