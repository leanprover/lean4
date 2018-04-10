open tactic
set_option pp.notation false
universe variables u
#check
λ (A : Type u) (a b c d : A) (H₁ : a = b) (H₂ : c = b) (H₃ : d = c),
have a = c, by do { transitivity, assumption, symmetry, assumption },
show a = d, by do { transitivity, this ← get_local "this", exact this, symmetry, assumption }
