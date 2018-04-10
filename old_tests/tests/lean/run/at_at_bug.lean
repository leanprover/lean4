example (a b : nat) (p : nat → nat → Prop) (h₁ : p a b) (h₂ : a = b) : p b b :=
@@eq.subst (λ x, p x b) h₂ h₁

set_option pp.all true

variable my_has_add : has_add nat
#check @@has_add.add my_has_add 0 1

local notation h1 `▸[` m `]` h2 := @@eq.subst m h1 h2

example (a b : nat) (p : nat → nat → Prop) (h₁ : p a b) (h₂ : a = b) : p b b :=
h₂ ▸[λ x, p x b] h₁
