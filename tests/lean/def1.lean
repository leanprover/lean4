set_option new_elaborator true

variable {A : Type}

lemma foo (f : A → A → A) (a b c : A) (H₁ : a = b) (H₂ : c = b) : f a = f c :=
H₂ ▸ eq.symm H₁ ▸ rfl
