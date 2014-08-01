----------------------------------------------------------------------------------------------------
-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Leonardo de Moura, Jeremy Avigad
----------------------------------------------------------------------------------------------------

import logic.connectives.basic


-- eq
-- --

inductive eq {A : Type} (a : A) : A → Prop :=
| refl : eq a a

infix `=`:50 := eq

theorem subst {A : Type} {a b : A} {P : A → Prop} (H1 : a = b) (H2 : P a) : P b :=
eq_rec H2 H1

theorem trans {A : Type} {a b c : A} (H1 : a = b) (H2 : b = c) : a = c :=
subst H2 H1

calc_subst subst
calc_refl  refl
calc_trans trans

theorem true_ne_false : ¬true = false :=
assume H : true = false,
  subst H trivial

theorem symm {A : Type} {a b : A} (H : a = b) : b = a :=
subst H (refl a)

namespace eq_proofs
  postfix `⁻¹`:100 := symm
  infixr `⬝`:75     := trans
  infixr `▸`:75    := subst
end
using eq_proofs

theorem congr1 {A : Type} {B : A → Type} {f g : Π x, B x} (H : f = g) (a : A) : f a = g a :=
H ▸ refl (f a)

theorem congr2 {A : Type} {B : Type} {a b : A} (f : A → B) (H : a = b) : f a = f b :=
H ▸ refl (f a)

theorem congr {A : Type} {B : Type} {f g : A → B} {a b : A} (H1 : f = g) (H2 : a = b) : f a = g b :=
H1 ▸ H2 ▸ refl (f a)

theorem equal_f {A : Type} {B : A → Type} {f g : Π x, B x} (H : f = g) : ∀x, f x = g x :=
take x, congr1 H x

theorem not_congr {a b : Prop} (H : a = b) : (¬a) = (¬b) :=
congr2 not H

theorem eqmp {a b : Prop} (H1 : a = b) (H2 : a) : b :=
H1 ▸ H2

infixl `<|`:100 := eqmp
infixl `◂`:100 := eqmp

theorem eqmpr {a b : Prop} (H1 : a = b) (H2 : b) : a :=
H1⁻¹ ◂ H2

theorem eqt_elim {a : Prop} (H : a = true) : a :=
H⁻¹ ◂ trivial

theorem eqf_elim {a : Prop} (H : a = false) : ¬a :=
assume Ha : a, H ◂ Ha

theorem imp_trans {a b c : Prop} (H1 : a → b) (H2 : b → c) : a → c :=
assume Ha, H2 (H1 Ha)

theorem imp_eq_trans {a b c : Prop} (H1 : a → b) (H2 : b = c) : a → c :=
assume Ha, H2 ◂ (H1 Ha)

theorem eq_imp_trans {a b c : Prop} (H1 : a = b) (H2 : b → c) : a → c :=
assume Ha, H2 (H1 ◂ Ha)

theorem eq_to_iff {a b : Prop} (H : a = b) : a ↔ b :=
iff_intro (λ Ha, H ▸ Ha) (λ Hb, H⁻¹ ▸ Hb)


-- ne
-- --

definition ne [inline] {A : Type} (a b : A) := ¬(a = b)
infix `≠`:50 := ne

theorem ne_intro {A : Type} {a b : A} (H : a = b → false) : a ≠ b := H

theorem ne_elim {A : Type} {a b : A} (H1 : a ≠ b) (H2 : a = b) : false := H1 H2

theorem a_neq_a_elim {A : Type} {a : A} (H : a ≠ a) : false := H (refl a)

theorem ne_irrefl {A : Type} {a : A} (H : a ≠ a) : false := H (refl a)

theorem ne_symm {A : Type} {a b : A} (H : a ≠ b) : b ≠ a :=
assume H1 : b = a, H (H1⁻¹)

theorem eq_ne_trans {A : Type} {a b c : A} (H1 : a = b) (H2 : b ≠ c) : a ≠ c := H1⁻¹ ▸ H2

theorem ne_eq_trans {A : Type} {a b c : A} (H1 : a ≠ b) (H2 : b = c) : a ≠ c := H2 ▸ H1

calc_trans eq_ne_trans
calc_trans ne_eq_trans