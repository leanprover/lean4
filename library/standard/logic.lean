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
prefix `¬`:40 := not

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

theorem absurd_not_true (H : ¬ true) : false
:= absurd trivial H

theorem not_false_trivial : ¬ false
:= assume H : false, H

inductive and (a b : Bool) : Bool :=
| and_intro : a → b → and a b

infixr `/\`:35 := and
infixr `∧`:35 := and

theorem and_elim {a b c : Bool} (H1 : a → b → c) (H2 : a ∧ b) : c
:= and_rec H1 H2

theorem and_elim_left {a b : Bool} (H : a ∧ b) : a
:= and_rec (λ a b, a) H

theorem and_elim_right {a b : Bool} (H : a ∧ b) : b
:= and_rec (λ a b, b) H

inductive or (a b : Bool) : Bool :=
| or_intro_left  : a → or a b
| or_intro_right : b → or a b

infixr `\/`:30 := or
infixr `∨`:30 := or

theorem or_elim {a b c : Bool} (H1 : a ∨ b) (H2 : a → c) (H3 : b → c) : c
:= or_rec H2 H3 H1

theorem resolve_right {a b : Bool} (H1 : a ∨ b) (H2 : ¬ a) : b
:= or_elim H1 (assume Ha, absurd_elim b Ha H2) (assume Hb, Hb)

theorem resolve_left {a b : Bool} (H1 : a ∨ b) (H2 : ¬ b) : a
:= or_elim H1 (assume Ha, Ha) (assume Hb, absurd_elim a Hb H2)

theorem or_flip {a b : Bool} (H : a ∨ b) : b ∨ a
:= or_elim H (assume Ha, or_intro_right b Ha) (assume Hb, or_intro_left a Hb)

inductive eq {A : Type} (a : A) : A → Bool :=
| refl : eq a a

infix `=`:50 := eq

theorem subst {A : Type} {a b : A} {P : A → Bool} (H1 : a = b) (H2 : P a) : P b
:= eq_rec H2 H1

theorem trans {A : Type} {a b c : A} (H1 : a = b) (H2 : b = c) : a = c
:= subst H2 H1

calc_subst subst
calc_refl  refl
calc_trans trans

theorem true_ne_false : ¬ true = false
:= assume H : true = false,
    subst H trivial

theorem symm {A : Type} {a b : A} (H : a = b) : b = a
:= subst H (refl a)

theorem congr1 {A : Type} {B : A → Type} {f g : Π x, B x} (H : f = g) (a : A) : f a = g a
:= subst H (refl (f a))

theorem congr2 {A : Type} {B : Type} {a b : A} (f : A → B) (H : a = b) : f a = f b
:= subst H (refl (f a))

theorem congr {A : Type} {B : Type} {f g : A → B} {a b : A} (H1 : f = g) (H2 : a = b) : f a = g b
:= subst H1 (subst H2 (refl (f a)))

theorem equal_f {A : Type} {B : A → Type} {f g : Π x, B x} (H : f = g) : ∀ x, f x = g x
:= take x, congr1 H x

theorem not_congr {a b : Bool} (H : a = b) : (¬ a) = (¬ b)
:= congr2 not H

theorem eqmp {a b : Bool} (H1 : a = b) (H2 : a) : b
:= subst H1 H2

infixl `<|`:100 := eqmp
infixl `◂`:100 := eqmp

theorem eqmpr {a b : Bool} (H1 : a = b) (H2 : b) : a
:= (symm H1) ◂ H2

theorem eqt_elim {a : Bool} (H : a = true) : a
:= (symm H) ◂ trivial

theorem eqf_elim {a : Bool} (H : a = false) : ¬ a
:= not_intro (assume Ha : a, H ◂ Ha)

theorem imp_trans {a b c : Bool} (H1 : a → b) (H2 : b → c) : a → c
:= assume Ha, H2 (H1 Ha)

theorem imp_eq_trans {a b c : Bool} (H1 : a → b) (H2 : b = c) : a → c
:= assume Ha, H2 ◂ (H1 Ha)

theorem eq_imp_trans {a b c : Bool} (H1 : a = b) (H2 : b → c) : a → c
:= assume Ha, H2 (H1 ◂ Ha)

definition ne {A : Type} (a b : A) := ¬ (a = b)
infix `≠`:50 := ne

theorem ne_intro {A : Type} {a b : A} (H : a = b → false) : a ≠ b
:= H

theorem ne_elim {A : Type} {a b : A} (H1 : a ≠ b) (H2 : a = b) : false
:= H1 H2

theorem a_neq_a_elim {A : Type} {a : A} (H : a ≠ a) : false
:= H (refl a)

theorem ne_irrefl {A : Type} {a : A} (H : a ≠ a) : false
:= H (refl a)

theorem ne_symm {A : Type} {a b : A} (H : a ≠ b) : b ≠ a
:= assume H1 : b = a, H (symm H1)

theorem eq_ne_trans {A : Type} {a b c : A} (H1 : a = b) (H2 : b ≠ c) : a ≠ c
:= subst (symm H1) H2

theorem ne_eq_trans {A : Type} {a b c : A} (H1 : a ≠ b) (H2 : b = c) : a ≠ c
:= subst H2 H1

calc_trans eq_ne_trans
calc_trans ne_eq_trans

definition iff (a b : Bool) := (a → b) ∧ (b → a)
infix `↔`:50 := iff

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

theorem eq_to_iff {a b : Bool} (H : a = b) : a ↔ b
:= iff_intro (λ Ha, subst H Ha) (λ Hb, subst (symm H) Hb)

inductive Exists {A : Type} (P : A → Bool) : Bool :=
| exists_intro : ∀ (a : A), P a → Exists P

notation `∃` binders `,` r:(scoped P, Exists P) := r

theorem exists_elim {A : Type} {P : A → Bool} {B : Bool} (H1 : ∃ x : A, P x) (H2 : ∀ (a : A) (H : P a), B) : B
:= Exists_rec H2 H1

definition exists_unique {A : Type} (p : A → Bool) := ∃ x, p x ∧ ∀ y, y ≠ x → ¬ p y

notation `∃!` binders `,` r:(scoped P, exists_unique P) := r

theorem exists_unique_intro {A : Type} {p : A → Bool} (w : A) (H1 : p w) (H2 : ∀ y, y ≠ w → ¬ p y) : ∃! x, p x
:= exists_intro w (and_intro H1 H2)

theorem exists_unique_elim {A : Type} {p : A → Bool} {b : Bool} (H2 : ∃! x, p x) (H1 : ∀ x, p x → (∀ y, y ≠ x → ¬ p y) → b) : b
:= obtain w Hw, from H2,
     H1 w (and_elim_left Hw) (and_elim_right Hw)

inductive inhabited (A : Type) : Bool :=
| inhabited_intro : A → inhabited A

theorem inhabited_elim {A : Type} {B : Bool} (H1 : inhabited A) (H2 : A → B) : B
:= inhabited_rec H2 H1

theorem inhabited_Bool [instance] : inhabited Bool
:= inhabited_intro true

theorem inhabited_fun [instance] (A : Type) {B : Type} (H : inhabited B) : inhabited (A → B)
:= inhabited_elim H (take (b : B), inhabited_intro (λ a : A, b))

definition cast {A B : Type} (H : A = B) (a : A) : B
:= eq_rec a H

theorem cast_refl {A : Type} (a : A) : cast (refl A) a = a
:= refl (cast (refl A) a)

theorem cast_proof_irrel {A B : Type} (H1 H2 : A = B) (a : A) : cast H1 a = cast H2 a
:= refl (cast H1 a)

theorem cast_eq {A : Type} (H : A = A) (a : A) : cast H a = a
:= calc cast H a = cast (refl A) a : cast_proof_irrel H (refl A) a
            ...  = a               : cast_refl a

definition heq {A B : Type} (a : A) (b : B) := ∃ H, cast H a = b

infixl `==`:50 := heq

theorem heq_type_eq {A B : Type} {a : A} {b : B} (H : a == b) : A = B
:= obtain w Hw, from H, w

theorem eq_to_heq {A : Type} {a b : A} (H : a = b) : a == b
:= exists_intro (refl A) (trans (cast_refl a) H)

theorem heq_to_eq {A : Type} {a b : A} (H : a == b) : a = b
:= obtain (w : A = A) (Hw : cast w a = b), from H,
    calc a = cast w a : symm (cast_eq w a)
      ...  = b        : Hw

theorem hrefl {A : Type} (a : A) : a == a
:= eq_to_heq (refl a)

theorem heqt_elim {a : Bool} (H : a == true) : a
:= eqt_elim (heq_to_eq H)

opaque_hint (hiding cast)

theorem hsubst {A B : Type} {a : A} {b : B} {P : ∀ (T : Type), T → Bool} (H1 : a == b) (H2 : P A a) : P B b
:= have Haux1 : ∀ H : A = A, P A (cast H a), from
     assume H : A = A, subst (symm (cast_eq H a)) H2,
   obtain (Heq : A = B) (Hw : cast Heq a = b), from H1,
   have Haux2 : P B (cast Heq a), from subst Heq Haux1 Heq,
     subst Hw Haux2

theorem hsymm {A B : Type} {a : A} {b : B} (H : a == b) : b == a
:= hsubst H (hrefl a)

theorem htrans {A B C : Type} {a : A} {b : B} {c : C} (H1 : a == b) (H2 : b == c) : a == c
:= hsubst H2 H1

theorem htrans_left {A B : Type} {a : A} {b c : B} (H1 : a == b) (H2 : b = c) : a == c
:= htrans H1 (eq_to_heq H2)

theorem htrans_right {A C : Type} {a b : A} {c : C} (H1 : a = b) (H2 : b == c) : a == c
:= htrans (eq_to_heq H1) H2

calc_trans htrans
calc_trans htrans_left
calc_trans htrans_right

theorem cast_heq {A B : Type} (H : A = B) (a : A) : cast H a == a
:= have H1 : ∀ (H : A = A) (a : A), cast H a == a, from
     λ H a, eq_to_heq (cast_eq H a),
   subst H H1 H a

theorem cast_eq_to_heq {A B : Type} {a : A} {b : B} {H : A = B} (H1 : cast H a = b) : a == b
:= calc a  == cast H a : hsymm (cast_heq H a)
       ... =  b        : H1
