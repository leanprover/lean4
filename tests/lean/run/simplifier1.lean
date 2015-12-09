constant P : Type₁
constant P_sub : subsingleton P
attribute P_sub [instance]
constant q : P → nat → Prop

set_option blast.simp false
set_option trace.blast true
set_option trace.cc true

example (a : nat) (h₁ h₂ : P) : q h₁ a = q h₂ a :=
by blast
