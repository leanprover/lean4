lemma subst_weirdness1 {α β : Type} {x : α} {P : Π t : Type, t → Prop}
  (H : β = α)
  (H' : P α x)
: P β (cast (by cc) x) :=
by { subst β, exact H' }

lemma subst_weirdness2 {α β : Type} {x : α} {P : Π t : Type, t → Prop}
  (H : β = α)
  (H' : P α x)
: P β (cast (by cc) x) :=
by { cases H, exact H' }

lemma subst_weirdness {α β : Type} {x : α} {P : Π t : Type, t → Prop}
  (H : β = α)
  (H' : P α x)
: P β (cast (by cc) x) :=
by { subst α, exact H' }
