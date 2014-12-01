prelude
definition bool : Type.{1} := Type.{0}
definition and (p q : bool) : bool
:= ∀ c : bool, (p → q → c) →  c
infixl `∧`:25 := and
theorem and_intro (p q : bool) (H1 : p) (H2 : q) : p ∧ q
:= λ (c : bool) (H : p → q → c), H H1 H2
theorem and_elim_left (p q : bool) (H : p ∧ q) : p
:= H p (λ (H1 : p) (H2 : q), H1)
theorem and_elim_right (p q : bool) (H : p ∧ q) : q
:= H q (λ (H1 : p) (H2 : q), H2)
theorem and_comm (p q : bool) (H : p ∧ q) : q ∧ p
:= have H1 : p, from and_elim_left p q H,
   have H2 : q, from and_elim_right p q H,
   show q ∧ p, from and_intro q p H2 H1
