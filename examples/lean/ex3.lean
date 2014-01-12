import macros.

theorem my_and_comm (a b : Bool) : (a ∧ b) → (b ∧ a)
:= assume H_ab, and_intro (and_elimr H_ab) (and_eliml H_ab).

theorem my_or_comm (a b : Bool) : (a ∨ b) → (b ∨ a)
:= assume H_ab,
      or_elim H_ab
         (λ H_a, or_intror b H_a)
         (λ H_b, or_introl H_b a).

-- (em a) is the excluded middle  a ∨ ¬a
-- (mt H H_na) is Modus Tollens with
--       H    : (a → b) → a)
--       H_na : ¬a
-- produces
--       ¬(a → b)
--
-- not_imp_eliml applied to
--        (MT H H_na) : ¬(a → b)
-- produces
--        a
theorem pierce (a b : Bool) : ((a → b) → a) → a
:= assume H, or_elim (em a)
               (λ H_a, H_a)
               (λ H_na, not_imp_eliml (mt H H_na)).

print environment 3.