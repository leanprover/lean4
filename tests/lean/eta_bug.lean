import logic
eval λ (A : Type) (x y : A) (H₁ : x = y) (H₂ : y = x), eq.trans H₁ H₂
-- Should not reduce to
-- λ (A : Type) (x y : A), eq.trans
