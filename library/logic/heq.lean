-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
import logic.eq

inductive heq {A : Type} (a : A) : Π {B : Type}, B → Prop :=
refl : heq a a
infixl `==`:50 := heq

namespace heq
  universe variable u
  variables {A B C : Type.{u}} {a a' : A} {b b' : B} {c : C}
  theorem drec_on {C : Π {B : Type} (b : B), a == b → Type} (H₁ : a == b) (H₂ : C a (refl a)) : C b H₁ :=
  rec (λ H₁ : a == a, show C a H₁, from H₂) H₁ H₁

  theorem subst {P : ∀T : Type, T → Prop} (H₁ : a == b) (H₂ : P A a) : P B b :=
  rec_on H₁ H₂

  theorem symm (H : a == b) : b == a :=
  subst H (refl a)

  theorem type_eq (H : a == b) : A = B :=
  subst H (eq.refl A)

  theorem from_eq (H : a = a') : a == a' :=
  eq.subst H (refl a)

  theorem to_eq (H : a == a') : a = a' :=
  have H₁ : ∀ (Ht : A = A), eq.rec_on Ht a = a, from
    take Ht, eq.refl (eq.rec_on Ht a),
  have H₂ : ∀ (Ht : A = A), eq.rec_on Ht a = a', from
    heq.rec_on H H₁,
  H₂ (type_eq H)

  theorem trans (H₁ : a == b) (H₂ : b == c) : a == c :=
  subst H₂ H₁

  theorem trans_left (H₁ : a == b) (H₂ : b = b') : a == b' :=
  trans H₁ (from_eq H₂)

  theorem trans_right (H₁ : a = a') (H₂ : a' == b) : a == b :=
  trans (from_eq H₁) H₂

  theorem true_elim {a : Prop} (H : a == true) : a :=
  eq_true_elim (heq.to_eq H)

end heq

calc_trans heq.trans
calc_trans heq.trans_left
calc_trans heq.trans_right
calc_symm  heq.symm
