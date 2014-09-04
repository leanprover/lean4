-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Leonardo de Moura, Jeremy Avigad

-- logic.connectives.eq
-- ====================

-- Equality.

import .prop

-- eq
-- --

inductive eq {A : Type} (a : A) : A → Prop :=
refl : eq a a

infix `=` := eq
notation `rfl` := refl _

theorem eq_id_refl {A : Type} {a : A} (H1 : a = a) : H1 = (refl a) := rfl

theorem eq_irrel {A : Type} {a b : A} (H1 H2 : a = b) : H1 = H2 := rfl

theorem subst {A : Type} {a b : A} {P : A → Prop} (H1 : a = b) (H2 : P a) : P b :=
eq.rec H2 H1

theorem trans {A : Type} {a b c : A} (H1 : a = b) (H2 : b = c) : a = c :=
subst H2 H1

calc_subst subst
calc_refl  refl
calc_trans trans

theorem symm {A : Type} {a b : A} (H : a = b) : b = a :=
subst H (refl a)

namespace eq_ops
  postfix `⁻¹` := symm
  infixr `⬝`   := trans
  infixr `▸`   := subst
end eq_ops
open eq_ops

theorem true_ne_false : ¬true = false :=
assume H : true = false,
  subst H trivial

-- eq_rec with arguments swapped, for transporting an element of a dependent type
definition eq_rec_on {A : Type} {a1 a2 : A} {B : A → Type} (H1 : a1 = a2) (H2 : B a1) : B a2 :=
eq.rec H2 H1

theorem eq_rec_on_id {A : Type} {a : A} {B : A → Type} (H : a = a) (b : B a) : eq_rec_on H b = b :=
refl (eq_rec_on rfl b)

theorem eq_rec_id {A : Type} {a : A} {B : A → Type} (H : a = a) (b : B a) : eq.rec b H = b :=
eq_rec_on_id H b

theorem eq_rec_on_compose {A : Type} {a b c : A} {P : A → Type} (H1 : a = b) (H2 : b = c)
    (u : P a) :
  eq_rec_on H2 (eq_rec_on H1 u) = eq_rec_on (trans H1 H2) u :=
(show ∀(H2 : b = c), eq_rec_on H2 (eq_rec_on H1 u) = eq_rec_on (trans H1 H2) u,
  from eq_rec_on H2 (take (H2 : b = b), eq_rec_on_id H2 _))
H2

theorem congr_fun {A : Type} {B : A → Type} {f g : Π x, B x} (H : f = g) (a : A) : f a = g a :=
H ▸ refl (f a)

theorem congr_arg {A : Type} {B : Type} {a b : A} (f : A → B) (H : a = b) : f a = f b :=
H ▸ refl (f a)

theorem congr {A : Type} {B : Type} {f g : A → B} {a b : A} (H1 : f = g) (H2 : a = b) :
  f a = g b :=
H1 ▸ H2 ▸ refl (f a)

theorem equal_f {A : Type} {B : A → Type} {f g : Π x, B x} (H : f = g) : ∀x, f x = g x :=
take x, congr_fun H x

theorem not_congr {a b : Prop} (H : a = b) : (¬a) = (¬b) :=
congr_arg not H

theorem eqmp {a b : Prop} (H1 : a = b) (H2 : a) : b :=
H1 ▸ H2

theorem eqmpr {a b : Prop} (H1 : a = b) (H2 : b) : a :=
H1⁻¹ ▸ H2

theorem eq_true_elim {a : Prop} (H : a = true) : a :=
H⁻¹ ▸ trivial

theorem eq_false_elim {a : Prop} (H : a = false) : ¬a :=
assume Ha : a, H ▸ Ha

theorem imp_trans {a b c : Prop} (H1 : a → b) (H2 : b → c) : a → c :=
assume Ha, H2 (H1 Ha)

theorem imp_eq_trans {a b c : Prop} (H1 : a → b) (H2 : b = c) : a → c :=
assume Ha, H2 ▸ (H1 Ha)

theorem eq_imp_trans {a b c : Prop} (H1 : a = b) (H2 : b → c) : a → c :=
assume Ha, H2 (H1 ▸ Ha)


-- ne
-- --

definition ne [inline] {A : Type} (a b : A) := ¬(a = b)
infix `≠` := ne

theorem ne_intro {A : Type} {a b : A} (H : a = b → false) : a ≠ b := H

theorem ne_elim {A : Type} {a b : A} (H1 : a ≠ b) (H2 : a = b) : false := H1 H2

theorem a_neq_a_elim {A : Type} {a : A} (H : a ≠ a) : false := H (refl a)

theorem ne_irrefl {A : Type} {a : A} (H : a ≠ a) : false := H (refl a)

theorem ne_symm {A : Type} {a b : A} (H : a ≠ b) : b ≠ a :=
assume H1 : b = a, H (H1⁻¹)

theorem eq_ne_trans {A : Type} {a b c : A} (H1 : a = b) (H2 : b ≠ c) : a ≠ c :=
H1⁻¹ ▸ H2

theorem ne_eq_trans {A : Type} {a b c : A} (H1 : a ≠ b) (H2 : b = c) : a ≠ c :=
H2 ▸ H1

calc_trans eq_ne_trans
calc_trans ne_eq_trans

theorem p_ne_false {p : Prop} (Hp : p) : p ≠ false :=
assume Heq : p = false, Heq ▸ Hp

theorem p_ne_true {p : Prop} (Hnp : ¬p) : p ≠ true :=
assume Heq : p = true, absurd trivial (Heq ▸ Hnp)
