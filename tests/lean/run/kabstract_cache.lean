open tactic

example {α : Type} (f : α → α → α) (a b : α) (H₁ : a = b) (H₂ : f b a = a) :
let c := a in f c c = c :=
by do dsimp,
      get_local `H₁ >>= rewrite_core reducible tt tt (occurrences.pos [1]) ff,
      get_local `H₂ >>= exact
