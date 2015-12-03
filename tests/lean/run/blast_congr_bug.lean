constant P : Type₁
constant P_sub : subsingleton P
attribute P_sub [instance]
constant q : P → Prop

section
set_option blast.simp true
set_option blast.cc   false

example (h₁ h₂ : P) : q h₁ = q h₂ :=
by blast
end


section
set_option blast.simp false
set_option blast.cc   true

example (h₁ h₂ : P) : q h₁ = q h₂ :=
by blast
end
