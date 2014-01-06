import macros.

theorem and_comm (a b : Bool) : (a ∧ b) ⇒ (b ∧ a)
:= assume H_ab, and::intro (and::elimr H_ab) (and::eliml H_ab).

theorem or_comm (a b : Bool) : (a ∨ b) ⇒ (b ∨ a)
:= assume H_ab,
      or::elim H_ab
         (λ H_a, or::intror b H_a)
         (λ H_b, or::introl H_b a).

-- (em a) is the excluded middle  a ∨ ¬a
-- (mt H H_na) is Modus Tollens with
--       H    : (a ⇒ b) ⇒ a)
--       H_na : ¬a
-- produces
--       ¬(a ⇒ b)
--
-- not::imp::eliml applied to
--        (MT H H_na) : ¬(a ⇒ b)
-- produces
--        a
theorem pierce (a b : Bool) : ((a ⇒ b) ⇒ a) ⇒ a
:= assume H, or::elim (em a)
                      (λ H_a, H_a)
                      (λ H_na, not::imp::eliml (mt H H_na)).

print environment 3.