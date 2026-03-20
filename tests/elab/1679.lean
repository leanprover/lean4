@[elab_as_elim] theorem Eq.subst' {α} {motive : α → Prop} {a b : α} :
  a = b → motive a → motive b := Eq.subst

example (P : α → Prop) {a b} (e : a = b) (h : P a) : P b :=
  Eq.subst' e h

example (P : α → Prop) {a b} (e : a = b) (h : P a) : P b :=
  e ▸ h
