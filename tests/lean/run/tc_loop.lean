open tactic

#elab (do { trace "foo", trace_state } : tactic unit)

#elab
λ (A : Type) (a b c d : A) (H₁ : a = b) (H₂ : c = b) (H₃ : d = c),
have a = c, by do { trace "have-expr...", trace_state, transitivity, assumption, symmetry, assumption },
show a = d, from sorry
