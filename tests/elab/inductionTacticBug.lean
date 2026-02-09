def ex {α} : Subsingleton (Squash α) := Subsingleton.intro $ by
  intro a b
  induction a using Squash.ind
  induction b using Squash.ind
  apply Quot.sound
  exact trivial
