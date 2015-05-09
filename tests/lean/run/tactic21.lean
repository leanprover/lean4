import logic
open tactic

theorem tst1 {A : Type} {a b c : A} {p : A → A → Prop} (H1 : p a b) (H2 : p b c) : ∃ x, p a x ∧ p x c
:= by apply exists.intro; apply and.intro; eassumption; eassumption

theorem tst2 {A : Type} {a b c d : A} {p : A → A → Prop} (Ha : p a c) (H1 : p a b) (Hb : p b d) (H2 : p b c) : ∃ x, p a x ∧ p x c
:= by apply exists.intro; apply and.intro; eassumption; eassumption

reveal tst2
(*
print(get_env():find("tst2"):value())
*)
