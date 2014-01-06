import macros.

theorem simple (p q r : Bool) : (p ⇒ q) ∧ (q ⇒ r) ⇒ p ⇒ r
:= assume H_pq_qr H_p,
        let P_pq := and::eliml H_pq_qr,
            P_qr := and::elimr H_pq_qr
        in P_qr ◂ (P_pq ◂ H_p)

setoption pp::implicit true.
print environment 1.

theorem simple2 (a b c : Bool) : (a ⇒ b ⇒ c) ⇒ (a ⇒ b) ⇒ a ⇒ c
:= assume H_abc H_ab H_a,
     (H_abc ◂ H_a) ◂ (H_ab ◂ H_a)

print environment 1.
