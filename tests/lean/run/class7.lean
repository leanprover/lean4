import logic
open tactic

inductive inh [class] (A : Type) : Type :=
intro : A -> inh A

theorem inh_bool [instance] : inh Prop
:= inh.intro true

set_option class.trace_instances true

theorem inh_fun [instance] {A B : Type} [H : inh B] : inh (A → B)
:= inh.rec (λ b, inh.intro (λ a : A, b)) H

theorem tst {A B : Type} (H : inh B) : inh (A → B → B)

theorem T1 {A : Type} (a : A) : inh A :=
by repeat (apply @inh.intro | eassumption)

theorem T2 : inh Prop
