-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
import .eq .quantifiers
open eq.ops

-- cast.lean
-- =========
definition cast {A B : Type} (H : A = B) (a : A) : B :=
eq.rec a H

theorem cast_refl {A : Type} (a : A) : cast (eq.refl A) a = a :=
rfl

theorem cast_proof_irrel {A B : Type} (H₁ H₂ : A = B) (a : A) : cast H₁ a = cast H₂ a :=
rfl

theorem cast_eq {A : Type} (H : A = A) (a : A) : cast H a = a :=
rfl

inductive heq.{l} {A : Type.{l}} (a : A) : Π {B : Type.{l}}, B → Prop :=
refl : heq a a
infixl `==`:50 := heq

namespace heq
  theorem rec_on {A B : Type} {a : A} {b : B} {C : Π {B : Type} (b : B), a == b → Type} (H₁ : a == b) (H₂ : C a (refl a)) : C b H₁ :=
  rec (λ H₁ : a == a, show C a H₁, from H₂) H₁ H₁

  theorem subst {A B : Type} {a : A} {b : B} {P : ∀T : Type, T → Prop} (H₁ : a == b) (H₂ : P A a) : P B b :=
  rec H₂ H₁

  theorem symm {A B : Type} {a : A} {b : B} (H : a == b) : b == a :=
  subst H (refl a)

  theorem type_eq {A B : Type} {a : A} {b : B} (H : a == b) : A = B :=
  subst H (eq.refl A)

  theorem from_eq {A : Type} {a b : A} (H : a = b) : a == b :=
  eq.subst H (refl a)

  theorem trans {A B C : Type} {a : A} {b : B} {c : C} (H₁ : a == b) (H₂ : b == c) : a == c :=
  subst H₂ H₁

  theorem trans_left {A B : Type} {a : A} {b c : B} (H₁ : a == b) (H₂ : b = c) : a == c :=
  trans H₁ (from_eq H₂)

  theorem trans_right {A C : Type} {a b : A} {c : C} (H₁ : a = b) (H₂ : b == c) : a == c :=
  trans (from_eq H₁) H₂

  theorem to_cast_eq {A B : Type} {a : A} {b : B} (H : a == b) : cast (type_eq H) a = b :=
  rec_on H !cast_eq

  theorem to_eq {A : Type} {a b : A} (H : a == b) : a = b :=
  calc a = cast (eq.refl A) a : !cast_eq⁻¹
     ... = b                  : to_cast_eq H

  theorem elim {A B : Type} {C : Prop} {a : A} {b : B} (H₁ : a == b)
    (H₂ : ∀ (Hab : A = B), cast Hab a = b → C) : C :=
  H₂ (type_eq H₁) (to_cast_eq H₁)

end heq

calc_trans heq.trans
calc_trans heq.trans_left
calc_trans heq.trans_right

theorem cast_heq {A B : Type} (H : A = B) (a : A) : cast H a == a :=
have H₁ : ∀ (H : A = A) (a : A), cast H a == a, from
assume H a, heq.from_eq (cast_eq H a),
eq.subst H H₁ H a

theorem cast_eq_to_heq {A B : Type} {a : A} {b : B} {H : A = B} (H₁ : cast H a = b) : a == b :=
calc a  == cast H a : heq.symm (cast_heq H a)
    ... =  b        : H₁

theorem heq.true_elim {a : Prop} (H : a == true) : a :=
eq_true_elim (heq.to_eq H)

theorem cast_trans {A B C : Type} (Hab : A = B) (Hbc : B = C) (a : A) :
  cast Hbc (cast Hab a) = cast (Hab ⬝ Hbc) a :=
heq.to_eq (calc cast Hbc (cast Hab a)   == cast Hab a          : cast_heq Hbc (cast Hab a)
                                   ...  == a                   : cast_heq Hab a
                                   ...  == cast (Hab ⬝ Hbc) a : heq.symm (cast_heq (Hab ⬝ Hbc) a))

theorem pi_eq {A : Type} {B B' : A → Type} (H : B = B') : (Π x, B x) = (Π x, B' x) :=
H ▸ (eq.refl (Π x, B x))

theorem dcongr_arg {A : Type} {B : A → Type} (f : Πx, B x) {a b : A} (H : a = b) : f a == f b :=
have e1 : ∀ (H : B a = B a), cast H (f a) = f a, from
  assume H, cast_eq H (f a),
have e2 : ∀ (H : B a = B b), cast H (f a) = f b, from
  H ▸ e1,
have e3 : cast (congr_arg B H) (f a) = f b, from
  e2 (congr_arg B H),
cast_eq_to_heq e3

theorem cast_app' {A : Type} {B B' : A → Type} (H : B = B') (f : Π x, B x) (a : A) :
  cast (pi_eq H) f a == f a :=
have H₁ : ∀ (H : (Π x, B x) = (Π x, B x)), cast H f a == f a, from
  assume H, heq.from_eq (congr_fun (cast_eq H f) a),
have H₂ : ∀ (H : (Π x, B x) = (Π x, B' x)), cast H f a == f a, from
  H ▸ H₁,
H₂ (pi_eq H)

theorem cast_pull {A : Type} {B B' : A → Type} (H : B = B') (f : Π x, B x) (a : A) :
                  cast (pi_eq H) f a = cast (congr_fun H a) (f a) :=
heq.to_eq (calc cast (pi_eq H) f a == f a                        : cast_app' H f a
                             ...   == cast (congr_fun H a) (f a) : heq.symm (cast_heq (congr_fun H a) (f a)))

theorem hcongr_fun' {A : Type} {B B' : A → Type} {f : Π x, B x} {f' : Π x, B' x} (a : A)
    (H₁ : f == f') (H₂ : B = B')
  : f a == f' a :=
heq.elim H₁ (λ (Ht : (Π x, B x) = (Π x, B' x)) (Hw : cast Ht f = f'),
  calc f a == cast (pi_eq H₂) f a  : heq.symm (cast_app' H₂ f a)
       ... =  cast Ht f a          : eq.refl (cast Ht f a)
       ... =  f' a                 : congr_fun Hw a)
