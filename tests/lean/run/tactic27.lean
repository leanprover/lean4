import logic
using tactic

definition my_tac := repeat ([ apply @and_intro
                             | apply @refl
                             ])
tactic_hint my_tac

theorem T1 {A : Type} {B : Type} (a : A) (b c : B) : a = a ∧ b = b ∧ c = c
