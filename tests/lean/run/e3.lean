definition Bool [inline] := Type.{0}

definition false := ∀x : Bool, x
check false

theorem false_elim (C : Bool) (H : false) : C
:= H C

definition eq {A : Type} (a b : A)
:= ∀ {P : A → Bool}, P a → P b

check eq

infix `=`:50 := eq

theorem refl {A : Type} (a : A) : a = a
:= λ P H, H

theorem subst {A : Type} {P : A -> Bool} {a b : A} (H1 : a = b) (H2 : P a) : P b
:= @H1 P H2

