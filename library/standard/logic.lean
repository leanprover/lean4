-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
definition Bool [inline] := Type.{0}

inductive false : Bool :=
-- No constructors

theorem false_elim (c : Bool) (H : false)
:= false_rec c H

inductive true : Bool :=
| trivial : true

definition not (a : Bool) := a → false
precedence `¬`:40
notation `¬` a := not a

notation `assume` binders `,` r:(scoped f, f) := r
notation `take`   binders `,` r:(scoped f, f) := r

theorem not_intro {a : Bool} (H : a → false) : ¬ a
:= H

theorem not_elim {a : Bool} (H1 : ¬ a) (H2 : a) : false
:= H1 H2

theorem absurd {a : Bool} (H1 : a) (H2 : ¬ a) : false
:= H2 H1

theorem mt {a b : Bool} (H1 : a → b) (H2 : ¬ b) : ¬ a
:= assume Ha : a, absurd (H1 Ha) H2

theorem contrapos {a b : Bool} (H : a → b) : ¬ b → ¬ a
:= assume Hnb : ¬ b, mt H Hnb

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
| refl : eq a a

infix `=` 50 := eq

theorem subst {A : Type} {a b : A} {P : A → Bool} (H1 : a = b) (H2 : P a) : P b
:= eq_rec H2 H1

theorem trans {A : Type} {a b c : A} (H1 : a = b) (H2 : b = c) : a = c
:= subst H2 H1

theorem symm {A : Type} {a b : A} (H : a = b) : b = a
:= subst H (refl a)

theorem congr1 {A B : Type} {f g : A → B} (H : f = g) (a : A) : f a = g a
:= subst H (refl (f a))

theorem congr2 {A B : Type} {a b : A} (f : A → B) (H : a = b) : f a = f b
:= subst H (refl (f a))

definition cast {A B : Type} (H : A = B) (a : A) : B
:= eq_rec a H

-- TODO(Leo): check why unifier needs 'help' in the following theorem
theorem cast_refl.{l} {A : Type.{l}} (a : A) : @cast.{l} A A (refl A) a = a
:= refl (@cast.{l} A A (refl A) a)

definition iff (a b : Bool) := (a → b) ∧ (b → a)
infix `↔` 50 := iff

theorem iff_intro {a b : Bool} (H1 : a → b) (H2 : b → a) : a ↔ b
:= and_intro H1 H2

theorem iff_elim {a b c : Bool} (H1 : (a → b) → (b → a) → c) (H2 : a ↔ b) : c
:= and_rec H1 H2

theorem iff_elim_left {a b : Bool} (H : a ↔ b) : a → b
:= iff_elim (assume H1 H2, H1) H

theorem iff_elim_right {a b : Bool} (H : a ↔ b) : b → a
:= iff_elim (assume H1 H2, H2) H

theorem iff_mp_left {a b : Bool} (H1 : a ↔ b) (H2 : a) : b
:= (iff_elim_left H1) H2

theorem iff_mp_right {a b : Bool} (H1 : a ↔ b) (H2 : b) : a
:= (iff_elim_right H1) H2

inductive Exists {A : Type} (P : A → Bool) : Bool :=
| exists_intro : ∀ (a : A), P a → Exists P

notation `∃` binders `,` r:(scoped P, Exists P) := r

theorem exists_elim {A : Type} {P : A → Bool} {B : Bool} (H1 : ∃ x : A, P x) (H2 : ∀ (a : A) (H : P a), B) : B
:= Exists_rec H2 H1

definition inhabited (A : Type) := ∃ x : A, true

theorem inhabited_intro {A : Type} (a : A) : inhabited A
:= exists_intro a trivial

theorem inhabited_elim {A : Type} {B : Bool} (H1 : inhabited A) (H2 : A → B) : B
:= exists_elim H1 (λ (a : A) (H : true), H2 a)

theorem inhabited_Bool : inhabited Bool
:= inhabited_intro true

theorem inhabited_fun (A : Type) {B : Type} (H : inhabited B) : inhabited (A → B)
:= inhabited_elim H (take (b : B), inhabited_intro (λ a : A, b))
