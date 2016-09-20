universe variable u
variable {A : Type u}

lemma foo (f : A → A → A) (a b c : A) (H₁ : a = b) (H₂ : c = b) : f a = f c :=
H₂ ▸ eq.symm H₁ ▸ rfl
