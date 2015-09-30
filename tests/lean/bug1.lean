prelude definition bool  : Type.{1}           := Type.{0}
definition and   (p q : bool) : bool  := ∀ c : bool, (p → q → c) → c
infixl ` ∧ `:25 := and

constant a : bool

-- Error
theorem and_intro1 (p q : bool) (H1 : p) (H2 : q) : a
:= fun (c : bool) (H : p -> q -> c), H H1 H2

-- Error
theorem and_intro2 (p q : bool) (H1 : p) (H2 : q) : p ∧ p
:= fun (c : bool) (H : p -> q -> c), H H1 H2

-- Error
theorem and_intro3 (p q : bool) (H1 : p) (H2 : q) : q ∧ p
:= fun (c : bool) (H : p -> q -> c), H H1 H2

-- Correct
theorem and_intro4 (p q : bool) (H1 : p) (H2 : q) : p ∧ q
:= fun (c : bool) (H : p -> q -> c), H H1 H2

check and_intro4
