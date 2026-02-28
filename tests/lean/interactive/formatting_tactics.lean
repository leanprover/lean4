theorem and_comm (p q :    Prop) (hp : p)   (hq : q) : q ∧ p := by
  constructor
  · exact    hq
  ·   exact hp

example (n :    Nat) : n + 0   = n := by
  simp
--^ formatting
