import logic
using num tactic

inductive inh (A : Type) : Type :=
inh_intro : A -> inh A

instance inh_intro

theorem inh_bool [instance] : inh Prop
:= inh_intro true

theorem inh_fun [instance] {A B : Type} (H : inh B) : inh (A → B)
:= inh_rec (λ b, inh_intro (λ a : A, b)) H

definition assump := eassumption; now

set_option elaborator.local_instances false
tactic_hint [inh] assump
tactic_hint assump

theorem tst {A B : Type} (H : inh B) : inh (A → B → B)

theorem T1 {A : Type} (a : A) : inh A

theorem T2 : inh Prop
