opaque R : Nat → Nat → Prop

@[grind ->]
axiom Rtrans {x y z : Nat} : R x y → R y z → R x z

@[grind →]
axiom Rtrans' {x y z : Nat} : R x y → R y z → R x z

@[grind <-]
axiom Rsymm {x y : Nat} : R x y → R y x

@[grind ←]
axiom Rsymm' {x y : Nat} : R x y → R y x

example : R a b → R b c → R d c → R a d := by
  grind only [-> Rtrans, <- Rsymm]

example : R a b → R b c → R d c → R a d := by
  grind only [→ Rtrans, ← Rsymm]
