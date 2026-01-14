module
axiom A : Type
axiom angle (x y z : A) : Int
axiom pi : Int
axiom Collinear (x y z : A) : Prop
axiom collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi {p₁ p₂ p₃ : A} :
  Collinear p₁ p₂ p₃ ↔ p₁ = p₂ ∨ p₃ = p₂ ∨ angle p₁ p₂ p₃ = 0 ∨ angle p₁ p₂ p₃ = pi

example {a b c a' b' c' : A} (h : ¬Collinear a b c)
    (ha₁ : angle a b c = angle a' b' c')
    (h' : angle a' b' c' = 0 ∨ angle a' b' c' = pi) :
    False := by
  grind only [collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi]
