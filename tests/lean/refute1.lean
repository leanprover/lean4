variables a b : Bool
axiom H : a /\ b
theorem T : a := by_contradiction (fun R, absurd (and_eliml H) R)
