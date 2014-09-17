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
definition rfl {A : Type} {a : A} := eq.refl a

namespace eq
  theorem id_refl {A : Type} {a : A} (H1 : a = a) : H1 = (eq.refl a) :=
  rfl

  theorem irrel {A : Type} {a b : A} (H1 H2 : a = b) : H1 = H2 :=
  rfl

  theorem subst {A : Type} {a b : A} {P : A → Prop} (H1 : a = b) (H2 : P a) : P b :=
  rec H2 H1

  theorem trans {A : Type} {a b c : A} (H1 : a = b) (H2 : b = c) : a = c :=
  subst H2 H1

  theorem symm {A : Type} {a b : A} (H : a = b) : b = a :=
  subst H (refl a)
end eq

calc_subst eq.subst
calc_refl  eq.refl
calc_trans eq.trans

namespace eq_ops
  postfix `⁻¹` := eq.symm
  infixr `⬝`   := eq.trans
  infixr `▸`   := eq.subst
end eq_ops
open eq_ops

namespace eq
  -- eq_rec with arguments swapped, for transporting an element of a dependent type
  definition rec_on {A : Type} {a1 a2 : A} {B : A → Type} (H1 : a1 = a2) (H2 : B a1) : B a2 :=
  eq.rec H2 H1

  theorem rec_on_id {A : Type} {a : A} {B : A → Type} (H : a = a) (b : B a) : rec_on H b = b :=
  refl (rec_on rfl b)

  theorem rec_id {A : Type} {a : A} {B : A → Type} (H : a = a) (b : B a) : rec b H = b :=
  rec_on_id H b

  theorem rec_on_compose {A : Type} {a b c : A} {P : A → Type} (H1 : a = b) (H2 : b = c)
          (u : P a) :
    rec_on H2 (rec_on H1 u) = rec_on (trans H1 H2) u :=
    (show ∀(H2 : b = c), rec_on H2 (rec_on H1 u) = rec_on (trans H1 H2) u,
      from rec_on H2 (take (H2 : b = b), rec_on_id H2 _))
    H2
end eq

theorem congr_fun {A : Type} {B : A → Type} {f g : Π x, B x} (H : f = g) (a : A) : f a = g a :=
H ▸ rfl

theorem congr_arg {A : Type} {B : Type} {a b : A} (f : A → B) (H : a = b) : f a = f b :=
H ▸ rfl

theorem congr {A : Type} {B : Type} {f g : A → B} {a b : A} (H1 : f = g) (H2 : a = b) :
  f a = g b :=
H1 ▸ H2 ▸ rfl

theorem equal_f {A : Type} {B : A → Type} {f g : Π x, B x} (H : f = g) : ∀x, f x = g x :=
take x, congr_fun H x

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

definition ne {A : Type} (a b : A) := ¬(a = b)
infix `≠` := ne

namespace ne
  theorem intro {A : Type} {a b : A} (H : a = b → false) : a ≠ b :=
  H

  theorem elim {A : Type} {a b : A} (H1 : a ≠ b) (H2 : a = b) : false :=
  H1 H2

  theorem irrefl {A : Type} {a : A} (H : a ≠ a) : false :=
  H rfl

  theorem symm {A : Type} {a b : A} (H : a ≠ b) : b ≠ a :=
  assume H1 : b = a, H (H1⁻¹)
end ne

theorem a_neq_a_elim {A : Type} {a : A} (H : a ≠ a) : false :=
H rfl

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

theorem true_ne_false : ¬true = false :=
assume H : true = false,
  H ▸ trivial
