open tactic

example (A : Type) (a₁ a₂ : A) (f : A → A) (H₀ : a₁ = a₂) : f a₁ = f a₂ := by simp_using_hs >> try reflexivity

example (A : Type) (a₁ a₁' a₂ a₂' : A) (f : A → A) (H₀ : a₁' = a₂') (H₁ : f a₁ = a₁') (H₂ : f a₂ = a₂')
: f a₁ = f a₂ := by simp_using_hs >> try reflexivity

constants (A : Type.{1}) (x y z w : A) (f : A → A) (H₁ : f (f x) = f y) (H₂ : f (f y) = f z) (H₃ : f (f z) = w)

definition foo : f (f (f (f x))) = w :=
by do h₁ ← mk_const `H₁,
      h₂ ← mk_const `H₂,
      h₃ ← mk_const `H₃,
      simp_using [h₁, h₂, h₃] >> try reflexivity
