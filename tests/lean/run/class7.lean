import logic
open tactic

inductive inh (A : Type) : Type :=
intro : A -> inh A

instance inh.intro

theorem inh_bool [instance] : inh Prop
:= inh.intro true

theorem inh_fun [instance] {A B : Type} (H : inh B) : inh (A → B)
:= inh.rec (λ b, inh.intro (λ a : A, b)) H

definition assump := eassumption; now

set_option elaborator.local_instances false
tactic_hint [inh] assump
tactic_hint assump

theorem tst {A B : Type} (H : inh B) : inh (A → B → B)

theorem T1 {A : Type} (a : A) : inh A

theorem T2 : inh Prop
