class Eq (α : Type) :=
(eq : α → α → Prop)
(ne : α → α → Prop := λ a b, ¬eq a b)
(eq := λ a b, ¬ne a b)

#check ({} : Eq ℕ)
#check ({eq := (=)} : Eq ℕ)
#check ({ne := (≠)} : Eq ℕ)
