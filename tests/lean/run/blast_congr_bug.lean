constant P : Type₁
constant P_sub : subsingleton P
attribute P_sub [instance]
constant q : P → Prop

section
example (h₁ h₂ : P) : q h₁ = q h₂ :=
by simp
end


section
set_option blast.strategy "cc"

example (h₁ h₂ : P) : q h₁ = q h₂ :=
by blast
end
