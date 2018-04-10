class inductive C {A : Type} : A → Prop

constant f {A : Type} (a : A) [H : C a] : Prop

noncomputable definition g {A : Type} (a b : A) {H1 : C a} {H2 : C b} : Prop :=
f a ∧ f b
