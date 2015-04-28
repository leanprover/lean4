import logic
open tactic

notation `(` h `|` r:(foldl `|` (e r, tactic.or_else r e) h) `)` := r

definition my_tac := repeat (apply @and.intro | apply @eq.refl)
tactic_hint my_tac

theorem T1 {A : Type} {B : Type} (a : A) (b c : B) : a = a ∧ b = b ∧ c = c
