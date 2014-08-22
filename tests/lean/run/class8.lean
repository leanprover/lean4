import standard
using num tactic prod

inductive inh (A : Type) : Prop :=
inh_intro : A -> inh A

instance inh_intro

theorem inh_elim {A : Type} {B : Prop} (H1 : inh A) (H2 : A → B) : B
:= inh_rec H2 H1

theorem inh_exists [instance] {A : Type} {P : A → Prop} (H : ∃x, P x) : inh A
:= obtain w Hw, from H, inh_intro w

theorem inh_bool [instance] : inh Prop
:= inh_intro true

theorem inh_fun [instance] {A B : Type} (H : inh B) : inh (A → B)
:= inh_rec (λb, inh_intro (λa : A, b)) H

theorem pair_inh [instance] {A : Type} {B : Type} (H1 : inh A) (H2 : inh B) : inh (prod A B)
:= inh_elim H1 (λa, inh_elim H2 (λb, inh_intro (pair a b)))

definition assump := eassumption
tactic_hint assump

theorem tst {A B : Type} (H : inh B) : inh (A → B → B)

theorem T1 {A B C D : Type} {P : C → Prop} (a : A) (H1 : inh B) (H2 : ∃x, P x) : inh ((A → A) × B × (D → C) × Prop)

(*
print(get_env():find("T1"):value())
*)