import macros

-- Well-founded relation definition
-- We are essentially saying that a relation R is well-founded
--    if every non-empty "set" P, has a R-minimal element
definition wf {A : (Type U)} (R : A → A → Bool) : Bool
:= ∀ P, (∃ w, P w) → ∃ min, P min ∧ ∀ b, R b min → ¬ P b

-- Well-founded induction theorem
theorem wf_induction {A : (Type U)} {R : A → A → Bool} {P : A → Bool} (Hwf : wf R) (iH : ∀ x, (∀ y, R y x → P y) → P x)
                     : ∀ x, P x
:= refute (λ N : ¬ ∀ x, P x,
     obtain (w : A) (Hw : ¬ P w), from not_forall_elim N,
         -- The main "trick" is to define Q x and ¬ P x.
         -- Since R is well-founded, there must be a R-minimal element r s.t. Q r (which is ¬ P r)
         let Q   : A → Bool                               := λ x, ¬ P x,
             Qw  : ∃ w, Q w                               := exists_intro w Hw,
             Qwf : ∃ min, Q min ∧ ∀ b, R b min → ¬ Q b  := Hwf Q Qw
         in obtain (r : A) (Hr : Q r ∧ ∀ b, R b r → ¬ Q b), from Qwf,
              -- Using the inductive hypothesis iH and Hr, we show P r, and derive the contradiction.
              let s1 : ∀ b, R b r → P b   := take b : A, assume H : R b r,
                                                 -- We are using Hr to derive ¬ ¬ P b
                                                 not_not_elim (and_elimr Hr b H),
                  s2 : P r                 := iH r s1,
                  s3 : ¬ P r               := and_eliml Hr
              in absurd s2 s3)
