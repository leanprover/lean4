variables a b : Bool
axiom H : a /\ b
theorem T : a := refute (fun R, absurd (and::eliml H) R)
