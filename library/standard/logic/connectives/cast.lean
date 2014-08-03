----------------------------------------------------------------------------------------------------
-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
----------------------------------------------------------------------------------------------------

import .eq .quantifiers

using eq_proofs

definition cast {A B : Type} (H : A = B) (a : A) : B :=
eq_rec a H

theorem cast_refl {A : Type} (a : A) : cast (refl A) a = a :=
refl (cast (refl A) a)

theorem cast_proof_irrel {A B : Type} (H1 H2 : A = B) (a : A) : cast H1 a = cast H2 a :=
refl (cast H1 a)

theorem cast_eq {A : Type} (H : A = A) (a : A) : cast H a = a :=
calc cast H a = cast (refl A) a : cast_proof_irrel H (refl A) a
         ...  = a               : cast_refl a

definition heq {A B : Type} (a : A) (b : B) :=
∃H, cast H a = b

infixl `==`:50 := heq

theorem heq_elim {A B : Type} {C : Prop} {a : A} {b : B} (H1 : a == b)
  (H2 : ∀ (Hab : A = B), cast Hab a = b → C) : C :=
obtain w Hw, from H1, H2 w Hw

theorem heq_type_eq {A B : Type} {a : A} {b : B} (H : a == b) : A = B :=
obtain w Hw, from H, w

theorem eq_to_heq {A : Type} {a b : A} (H : a = b) : a == b :=
exists_intro (refl A) (cast_refl a ⬝ H)

theorem heq_to_eq {A : Type} {a b : A} (H : a == b) : a = b :=
obtain (w : A = A) (Hw : cast w a = b), from H,
calc a = cast w a : (cast_eq w a)⁻¹
  ...  = b        : Hw

theorem hrefl {A : Type} (a : A) : a == a :=
eq_to_heq (refl a)

theorem heqt_elim {a : Prop} (H : a == true) : a :=
eqt_elim (heq_to_eq H)

opaque_hint (hiding cast)

theorem hsubst {A B : Type} {a : A} {b : B} {P : ∀ (T : Type), T → Prop} (H1 : a == b)
  (H2 : P A a) : P B b :=
have Haux1 : ∀ H : A = A, P A (cast H a), from
  assume H : A = A, (cast_eq H a)⁻¹ ▸ H2,
obtain (Heq : A = B) (Hw : cast Heq a = b), from H1,
have Haux2 : P B (cast Heq a), from subst Heq Haux1 Heq,
Hw ▸ Haux2

theorem hsymm {A B : Type} {a : A} {b : B} (H : a == b) : b == a :=
hsubst H (hrefl a)

theorem htrans {A B C : Type} {a : A} {b : B} {c : C} (H1 : a == b) (H2 : b == c) : a == c :=
hsubst H2 H1

theorem htrans_left {A B : Type} {a : A} {b c : B} (H1 : a == b) (H2 : b = c) : a == c :=
htrans H1 (eq_to_heq H2)

theorem htrans_right {A C : Type} {a b : A} {c : C} (H1 : a = b) (H2 : b == c) : a == c :=
htrans (eq_to_heq H1) H2

calc_trans htrans
calc_trans htrans_left
calc_trans htrans_right

theorem type_eq {A B : Type} {a : A} {b : B} (H : a == b) : A = B :=
hsubst H (refl A)

theorem cast_heq {A B : Type} (H : A = B) (a : A) : cast H a == a :=
have H1 : ∀ (H : A = A) (a : A), cast H a == a, from
  assume H a, eq_to_heq (cast_eq H a),
subst H H1 H a

theorem cast_eq_to_heq {A B : Type} {a : A} {b : B} {H : A = B} (H1 : cast H a = b) : a == b :=
calc a  == cast H a : hsymm (cast_heq H a)
    ... =  b        : H1

theorem cast_trans {A B C : Type} (Hab : A = B) (Hbc : B = C) (a : A) :
  cast Hbc (cast Hab a) = cast (Hab ⬝ Hbc) a :=
heq_to_eq (calc cast Hbc (cast Hab a)   == cast Hab a        : cast_heq Hbc (cast Hab a)
                                   ...  == a                 : cast_heq Hab a
                                   ...  == cast (Hab ⬝ Hbc) a : hsymm (cast_heq (Hab ⬝ Hbc) a))

theorem dcongr2 {A : Type} {B : A → Type} (f : Πx, B x) {a b : A} (H : a = b) : f a == f b :=
have e1 : ∀ (H : B a = B a), cast H (f a) = f a, from
  assume H, cast_eq H (f a),
have e2 : ∀ (H : B a = B b), cast H (f a) = f b, from
  subst H e1,
have e3 : cast (congr2 B H) (f a) = f b, from
  e2 (congr2 B H),
cast_eq_to_heq e3

theorem pi_eq {A : Type} {B B' : A → Type} (H : B = B') : (Π x, B x) = (Π x, B' x) :=
subst H (refl (Π x, B x))

theorem cast_app' {A : Type} {B B' : A → Type} (H : B = B') (f : Π x, B x) (a : A) :
  cast (pi_eq H) f a == f a :=
have H1 : ∀ (H : (Π x, B x) = (Π x, B x)), cast H f a == f a, from
  assume H, eq_to_heq (congr1 (cast_eq H f) a),
have H2 : ∀ (H : (Π x, B x) = (Π x, B' x)), cast H f a == f a, from
  subst H H1,
H2 (pi_eq H)

theorem cast_pull {A : Type} {B B' : A → Type} (H : B = B') (f : Π x, B x) (a : A) :
                  cast (pi_eq H) f a = cast (congr1 H a) (f a) :=
heq_to_eq (calc cast (pi_eq H) f a == f a                     : cast_app' H f a
                             ...   == cast (congr1 H a) (f a) : hsymm (cast_heq (congr1 H a) (f a)))

theorem hcongr1' {A : Type} {B B' : A → Type} {f : Π x, B x} {f' : Π x, B' x} (a : A)
    (H1 : f == f') (H2 : B = B')
  : f a == f' a :=
heq_elim H1 (λ (Ht : (Π x, B x) = (Π x, B' x)) (Hw : cast Ht f = f'),
  calc f a == cast (pi_eq H2) f a  : hsymm (cast_app' H2 f a)
       ... =  cast Ht f a          : refl (cast Ht f a)
       ... =  f' a                 : congr1 Hw a)
