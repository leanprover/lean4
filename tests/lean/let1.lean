prelude -- Correct version
check let bool                      := Type.{0},
          and  (p q : bool)         := ∀ c : bool, (p → q → c) → c,
          infixl `∧`:25             := and,
          and_intro (p q : bool) (H1 : p) (H2 : q) : p ∧ q
              := λ (c : bool) (H : p → q → c), H H1 H2,
          and_elim_left  (p q : bool) (H : p ∧ q) : p
              := H p (λ (H1 : p) (H2 : q), H1),
          and_elim_right (p q : bool) (H : p ∧ q) : q
              := H q (λ (H1 : p) (H2 : q), H2)
       in and_intro

-- TODO(Leo): fix expected output as soon as elaborator starts checking let-expression type again

check let bool                := Type.{0},
          and  (p q : bool)   := ∀ c : bool, (p → q → c) → c,
          infixl `∧`:25       := and,
          and_intro [visible] (p q : bool) (H1 : p) (H2 : q) : q ∧ p
              := λ (c : bool) (H : p → q → c), H H1 H2,
          and_elim_left  (p q : bool) (H : p ∧ q) : p
              := H p (λ (H1 : p) (H2 : q), H1),
          and_elim_right (p q : bool) (H : p ∧ q) : q
              := H q (λ (H1 : p) (H2 : q), H2)
       in and_intro
