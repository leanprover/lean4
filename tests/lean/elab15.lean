open tactic

set_option pp.notation false

check
λ (A : Type) (a b c d : A) (H₁ : a = b) (H₂ : c = b) (H₃ : d = c),
have a = c, by do { transitivity, assumption, symmetry, assumption },
show a = d, by do { transitivity, this ← get_local "this", exact this, symmetry, assumption }
