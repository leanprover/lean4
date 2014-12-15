prelude
definition Prop := Type.{0}

definition false := ∀x : Prop, x
check false

theorem false.elim (C : Prop) (H : false) : C
:= H C

definition eq {A : Type} (a b : A)
:= ∀ {P : A → Prop}, P a → P b

check eq

infix `=`:50 := eq

theorem refl {A : Type} (a : A) : a = a
:= λ P H, H

theorem subst {A : Type} {P : A -> Prop} {a b : A} (H1 : a = b) (H2 : P a) : P b
:= @H1 P H2
