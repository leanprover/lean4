axiom all {A : Type}: list A → (A → Prop) → Prop
variable {A : Type}
variable {R : A → A → Prop}
set_option pp.all true
#check ∀ a l, all l (R a)
