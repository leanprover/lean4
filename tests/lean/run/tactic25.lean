import logic
open tactic

definition my_tac1 := apply @eq.refl
definition my_tac2 := repeat (apply @and.intro; assumption)

tactic_hint my_tac1
tactic_hint my_tac2

theorem T1 {A : Type.{2}} (a : A) : a = a

theorem T2 {a b c : Prop} (Ha : a) (Hb : b) (Hc : c) : a ∧ b ∧ c

definition my_tac3 := fixpoint (λ f, (apply @or.intro_left; f  |
                                      apply @or.intro_right; f |
                                      assumption))

tactic_hint my_tac3
theorem T3 {a b c : Prop} (Hb : b) : a ∨ b ∨ c
