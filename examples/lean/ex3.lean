Import macros.

Theorem and_comm (a b : Bool) : (a ∧ b) ⇒ (b ∧ a)
:= Assume H_ab, Conj (Conjunct2 H_ab) (Conjunct1 H_ab).

Theorem or_comm (a b : Bool) : (a ∨ b) ⇒ (b ∨ a)
:= Assume H_ab,
      DisjCases H_ab
                (λ H_a, Disj2 b H_a)
                (λ H_b, Disj1 H_b a).

-- (EM a) is the excluded middle  a ∨ ¬a
-- (MT H H_na) is Modus Tollens with
--       H    : (a ⇒ b) ⇒ a)
--       H_na : ¬a
-- produces
--       ¬(a ⇒ b)
--
-- NotImp1 applied to
--        (MT H H_na) : ¬(a ⇒ b)
-- produces
--        a
Theorem pierce (a b : Bool) : ((a ⇒ b) ⇒ a) ⇒ a
:= Assume H, DisjCases (EM a)
                       (λ H_a, H_a)
                       (λ H_na, NotImp1 (MT H H_na)).

print Environment 3.