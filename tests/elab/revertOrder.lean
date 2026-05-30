example (a b c : Nat) : a * b * c = a * b * c := by
  revert c a b
  guard_target = forall (c a b : Nat), a * b * c = a * b * c
  intro c a b
  rfl
