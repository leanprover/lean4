open tactic

example {α : Type} (f : α → α → α) (a b : α) (H₁ : a = b) (H₂ : f b a = a) :
let c := a in f c c = c :=
by do dsimp,
      e ← get_local `H₁, rewrite_target e {occs := occurrences.pos [1]},
      get_local `H₂ >>= exact
