
universe u
variable {α : Type u} {p : α → Prop}

theorem ex (a : α) (h1 h2 : p a) (h : Subtype.mk a h1 = Subtype.mk a h1) : Subtype.mk a h1 = Subtype.mk a h2 :=
h
