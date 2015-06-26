import data.list
constant R : Π {A : Type}, A → A → Prop
infix `~` := R

example {A : Type} {a b c d : list nat} (H₁ : a ~ b) (H₂ : b = c) (H₃ : c = d) : a ~ d :=
calc a ~ b : H₁
   ... = c : H₂
   ... = d : H₃

example {A : Type} {a b c d : list nat} (H₁ : a = b) (H₂ : b = c) (H₃ : c ~ d) : a ~ d :=
calc a = b : H₁
   ... = c : H₂
   ... ~ d : H₃

example {A : Type} {a b c d : list nat} (H₁ : a = b) (H₂ : b ~ c) (H₃ : c = d) : a ~ d :=
calc a = b : H₁
   ... ~ c : H₂
   ... = d : H₃
