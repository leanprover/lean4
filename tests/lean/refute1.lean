Variables a b : Bool
Axiom H : a /\ b
Theorem T : a := Refute (fun R, Absurd (Conjunct1 H) R)
