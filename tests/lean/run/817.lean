variables A B : Prop
premises (H₁ : A) (H₂ : A → B)

example : B :=
suffices A ∧ (A → B), from and.right this (and.left this),
and.intro H₁ H₂

example : B :=
suffices H : A ∧ (A → B), from and.right H (and.left H),
and.intro H₁ H₂
