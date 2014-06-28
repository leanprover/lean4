definition Bool [inline] := Type.{0}

inductive false : Bool :=
-- No constructors

theorem false_elim (c : Bool) (H : false)
:= @false_rec c H

inductive true : Bool :=
| trivial : true

definition not (a : Bool) := a → false
precedence `¬`:40
notation `¬` a := not a

theorem not_intro {a : Bool} (H : a → false) : ¬ a
:= H

theorem not_elim {a : Bool} (H1 : ¬ a) (H2 : a) : false
:= H1 H2

theorem absurd {a : Bool} (H1 : a) (H2 : ¬ a) : false
:= H2 H1

theorem mt {a b : Bool} (H1 : a → b) (H2 : ¬ b) : ¬ a
:= λ Ha : a, absurd (H1 Ha) H2

theorem contrapos {a b : Bool} (H : a → b) : ¬ b → ¬ a
:= λ Hnb : ¬ b, mt H Hnb

theorem absurd_elim {a : Bool} (b : Bool) (H1 : a) (H2 : ¬ a) : b
:= false_elim b (absurd H1 H2)

inductive and (a b : Bool) : Bool :=
| and_intro : a → b → and a b

infixr `/\` 35 := and
infixr `∧`  35 := and

theorem and_elim_left {a b : Bool} (H : a ∧ b) : a
:= and_rec (λ a b, a) H

theorem and_elim_right {a b : Bool} (H : a ∧ b) : b
:= and_rec (λ a b, b) H

inductive or (a b : Bool) : Bool :=
| or_intro_left  : a → or a b
| or_intro_right : b → or a b

infixr `\/` 30 := or
infixr `∨` 30 := or

theorem or_elim (a b c : Bool) (H1 : a ∨ b) (H2 : a → c) (H3 : b → c) : c
:= or_rec H2 H3 H1

inductive eq {A : Type} (a : A) : A → Bool :=
| eq_intro : eq A a a  -- TODO: use elaborator in inductive_cmd module, we should not need to type A here

infix `=` 50 := eq

theorem refl {A : Type} (a : A) : a = a
:= @eq_intro A a

theorem subst {A : Type} {a b : A} {P : A → Bool} (H1 : a = b) (H2 : P a) : P b
:= eq_rec H2 H1

theorem trans {A : Type} {a b c : A} (H1 : a = b) (H2 : b = c) : a = c
:= subst H2 H1

theorem symm {A : Type} {a b : A} (H : a = b) : b = a
:= subst H (refl a)

-- theorem congr1 {A B : Type} {f g : A → B} (H : f = g) (a : A) : f a = g a
-- := subst H (refl (f a)) -- TODO: check unifier does not work in this case

theorem congr2 {A B : Type} {a b : A} (f : A → B) (H : a = b) : f a = f b
:= subst H (refl (f a))
