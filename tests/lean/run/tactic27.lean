import logic
open tactic

definition my_tac := repeat (apply @and.intro | apply @eq.refl)
tactic_hint my_tac

theorem T1 {A : Type} {B : Type} (a : A) (b c : B) : a = a ∧ b = b ∧ c = c
