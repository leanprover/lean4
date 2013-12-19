Theorem simple (p q r : Bool) : (p ⇒ q) ∧ (q ⇒ r) ⇒ p ⇒ r :=
    Discharge (λ H_pq_qr, Discharge (λ H_p,
        let P_pq := Conjunct1 H_pq_qr,
            P_qr := Conjunct2 H_pq_qr,
            P_q  := MP P_pq H_p
        in MP P_qr P_q))

SetOption pp::implicit true
Show Environment 1

Theorem simple2 (a b c : Bool) : (a ⇒ b ⇒ c) ⇒ (a ⇒ b) ⇒ a ⇒ c :=
    Discharge (λ H_abc, Discharge (λ H_ab, Discharge (λ H_a,
        let P_b  := (MP H_ab H_a),
            P_bc := (MP H_abc H_a)
        in MP P_bc P_b)))

Show Environment 1
