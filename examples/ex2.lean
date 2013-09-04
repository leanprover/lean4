Theorem simple (p q r : Bool) : (p ⇒ q) ∧ (q ⇒ r) ⇒ p ⇒ r :=
    Discharge (λ H1, Discharge (λ H2, MP (Conjunct2 H1) (MP (Conjunct1 H1) H2)))

Set pp::implicit true
Show Environment 1

