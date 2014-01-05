import macros.

theorem simple (p q r : Bool) : (p ⇒ q) ∧ (q ⇒ r) ⇒ p ⇒ r
:= Assume H_pq_qr H_p,
        let P_pq := Conjunct1 H_pq_qr,
            P_qr := Conjunct2 H_pq_qr,
            P_q  := MP P_pq H_p
        in MP P_qr P_q.

setoption pp::implicit true.
print environment 1.

theorem simple2 (a b c : Bool) : (a ⇒ b ⇒ c) ⇒ (a ⇒ b) ⇒ a ⇒ c
:= Assume H_abc H_ab H_a,
        let P_b  := (MP H_ab H_a),
            P_bc := (MP H_abc H_a)
        in MP P_bc P_b.

print environment 1.
