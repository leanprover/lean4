-- Annotating lemmas

theorem simple (p q r : Bool) : (p → q) ∧ (q → r) → p → r :=
    λ H_pq_qr H_p,
        let P_pq : (p → q) := and::eliml H_pq_qr,
            P_qr : (q → r) := and::elimr H_pq_qr,
            P_q  : q        := P_pq H_p
        in P_qr P_q

print environment 1