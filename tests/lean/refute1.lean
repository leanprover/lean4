variables a b : Bool
axiom H : a /\ b
theorem T : a := Refute (fun R, Absurd (Conjunct1 H) R)
