prelude
definition Prop := Sort.{0}

definition false : Prop := ∀x : Prop, x
check false

theorem false.elim (C : Prop) (H : false) : C
:= H C

definition Eq {A : Type} (a b : A)
:= ∀ P : A → Prop, P a → P b

check Eq

infix `=`:50 := Eq

theorem refl {A : Type} (a : A) : a = a
:= λ P H, H

definition true : Prop
:= false = false

theorem trivial : true
:= refl false

attribute [elab_as_eliminator]
theorem subst {A : Type} {P : A -> Prop} {a b : A} (H1 : a = b) (H2 : P a) : P b
:= H1 _ H2

theorem symm {A : Type} {a b : A} (H : a = b) : b = a
:= subst H (refl a)

theorem trans {A : Type} {a b c : A} (H1 : a = b) (H2 : b = c) : a = c
:= subst H2 H1
