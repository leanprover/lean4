structure S where
  f : Nat → Nat

example (h : g 1 = x) : { f := g : S }.f 1 = x := by
  unfold S.f
  dsimp
  guard_target =ₛ g 1 = x
  assumption
