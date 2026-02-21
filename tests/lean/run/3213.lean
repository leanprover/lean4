set_option pp.proofs true
variable (P Q : Prop) (A : Type) (f : P → Q → A) (x : P ∧ Q)

example : And.rec f ⟨x.1,x.2⟩ = f (And.left x) (And.right x) := rfl
example : (And.rec f ⟨x.1,x.2⟩ : A) = And.rec f x  := rfl
