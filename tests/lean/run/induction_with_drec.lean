universe u

example {α β : Type u} (a : α) (b : β) (h : α = β) : (eq.rec_on h a : β) = b → a = eq.rec_on (h^.symm) b :=
by induction h; intros; assumption
