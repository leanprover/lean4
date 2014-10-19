import logic data.sigma data.list
open sigma

check ∃ (A : Type₁) (x y : A), x = y
check ∃ (x : num), x = 0
check Σ (x : num), x = 10
check Σ (A : Type₁), list A
