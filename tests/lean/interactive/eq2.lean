-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Leonardo de Moura, Jeremy Avigad, Floris van Doorn

-- logic.connectives.eq
-- ====================

-- Equality.

import logic.core.prop

-- eq
-- --

inductive eq {A : Type} (a : A) : A → Prop :=
refl : eq a a

infix `=` := eq
definition rfl {A : Type} {a : A} := eq.refl a

-- proof irrelevance is built in
theorem proof_irrel {a : Prop} {H1 H2 : a} : H1 = H2 := rfl

namespace eq
  theorem id_refl {A : Type} {a : A} (H1 : a = a) : H1 = (eq.refl a) :=
  proof_irrel

  theorem irrel {A : Type} {a b : A} (H1 H2 : a = b) : H1 = H2 :=
  proof_irrel

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

  -- definition rec_on {A : Type} {a1 a2 : A} {B : A → Type} (H1 : a1 = a2) (H2 : B a1) : B a2 :=
  -- eq.rec H2 H1

  definition rec_on {A : Type} {a a' : A} {B : Πa' : A, a = a' → Type} (H1 : a = a') (H2 : B a (refl a)) : B a' H1 :=
  eq.rec (λH1 : a = a, show B a H1, from H2) H1 H1

  theorem rec_on_id {A : Type} {a : A} {B : Πa' : A, a = a' → Type} (H : a = a) (b : B a H) : rec_on H b = b :=
  refl (rec_on rfl b)

  theorem rec_on_constant {A : Type} {a a' : A} {B : Type} (H : a = a') (b : B) : rec_on H b = b :=
  rec_on H (λ(H' : a = a), rec_on_id H' b) H

  theorem rec_on_constant2 {A : Type} {a₁ a₂ a₃ a₄ : A} {B : Type} (H₁ : a₁ = a₂) (H₂ : a₃ = a₄) (b : B) : rec_on H₁ b = rec_on H₂ b :=
  rec_on_constant H₁ b ⬝ rec_on_constant H₂ b ⁻¹

  theorem rec_on_irrel {A B : Type} {a a' : A} {f : A → B} {D : B → Type} (H : a = a') (H' : f a = f a') (b : D (f a)) : rec_on H b = rec_on H' b :=
  rec_on H (λ(H : a = a) (H' : f a = f a), rec_on_id H b ⬝ rec_on_id H' b⁻¹) H H'

  theorem rec_id {A : Type} {a : A} {B : A → Type} (H : a = a) (b : B a) : rec b H = b :=
  id_refl H⁻¹ ▸ refl (eq.rec b (refl a))

  theorem rec_on_compose {A : Type} {a b c : A} {P : A → Type} (H1 : a = b) (H2 : b = c)
          (u : P a) :
    rec_on H2 (rec_on H1 u) = rec_on (trans H1 H2) u :=
    (show ∀(H2 : b = c), rec_on H2 (rec_on H1 u) = rec_on (trans H1 H2) u,
      from rec_on H2 (take (H2 : b = b), rec_on_id H2 _))
    H2
end eq

open eq

theorem congr_fun {A : Type} {B : A → Type} {f g : Π x, B x} (H : f = g) (a : A) : f a = g a :=
H ▸ rfl

theorem congr_arg {A : Type} {B : Type} {a b : A} (f : A → B) (H : a = b) : f a = f b :=
H ▸ rfl

theorem congr {A : Type} {B : Type} {f g : A → B} {a b : A} (H1 : f = g) (H2 : a = b) :
  f a = g b :=
H1 ▸ H2 ▸ rfl

theorem congr_arg2 {A B C : Type} {a a' : A} {b b' : B} (f : A → B → C) (Ha : a = a') (Hb : b = b') : f a b = f a' b' :=
congr (congr_arg f Ha) Hb

theorem congr_arg3 {A B C D : Type} {a a' : A} {b b' : B} {c c' : C} (f : A → B → C → D) (Ha : a = a') (Hb : b = b') (Hc : c = c') : f a b c = f a' b' c' :=
congr (congr_arg2 f Ha Hb) Hc

theorem congr_arg4 {A B C D E : Type} {a a' : A} {b b' : B} {c c' : C} {d d' : D} (f : A → B → C → D → E) (Ha : a = a') (Hb : b = b') (Hc : c = c') (Hd : d = d') : f a b c d = f a' b' c' d' :=
congr (congr_arg3 f Ha Hb Hc) Hd

theorem congr_arg5 {A B C D E F : Type} {a a' : A} {b b' : B} {c c' : C} {d d' : D} {e e' : E} (f : A → B → C → D → E → F) (Ha : a = a') (Hb : b = b') (Hc : c = c') (Hd : d = d') (He : e = e') : f a b c d e = f a' b' c' d' e' :=
congr (congr_arg4 f Ha Hb Hc Hd) He

theorem congr2 {A B C : Type} {a a' : A} {b b' : B} (f f' : A → B → C) (Hf : f = f') (Ha : a = a') (Hb : b = b') : f a b = f' a' b' :=
Hf ▸ congr_arg2 f Ha Hb

theorem congr3 {A B C D : Type} {a a' : A} {b b' : B} {c c' : C} (f f' : A → B → C → D) (Hf : f = f') (Ha : a = a') (Hb : b = b') (Hc : c = c') : f a b c = f' a' b' c' :=
Hf ▸ congr_arg3 f Ha Hb Hc

theorem congr4 {A B C D E : Type} {a a' : A} {b b' : B} {c c' : C} {d d' : D} (f f' : A → B → C → D → E) (Hf : f = f') (Ha : a = a') (Hb : b = b') (Hc : c = c') (Hd : d = d') : f a b c d = f' a' b' c' d' :=
Hf ▸ congr_arg4 f Ha Hb Hc Hd

theorem congr5 {A B C D E F : Type} {a a' : A} {b b' : B} {c c' : C} {d d' : D} {e e' : E} (f f' : A → B → C → D → E → F) (Hf : f = f') (Ha : a = a') (Hb : b = b') (Hc : c = c') (Hd : d = d') (He : e = e') : f a b c d e = f' a' b' c' d' e' :=
Hf ▸ congr_arg5 f Ha Hb Hc Hd He

theorem congr_arg2_dep {A : Type} {B : A → Type} {C : Type} {a₁ a₂ : A}
    {b₁ : B a₁} {b₂ : B a₂} (f : Πa, B a → C) (H₁ : a₁ = a₂) (H₂ : eq.rec_on H₁ b₁ = b₂) :
    f a₁ b₁ = f a₂ b₂ :=
  eq.rec_on H₁
    (λ (b₂ : B a₁) (H₁ : a₁ = a₁) (H₂ : eq.rec_on H₁ b₁ = b₂),
      calc
        f a₁ b₁ = f a₁ (eq.rec_on H₁ b₁) : {(eq.rec_on_id H₁ b₁)⁻¹}
            ... = f a₁ b₂                : {H₂})
    b₂ H₁ H₂

theorem congr_arg3_dep {A : Type} {B : A → Type} {C : Πa, B a → Type} {D : Type} {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂} {c₁ : C a₁ b₁} {c₂ : C a₂ b₂} (f : Πa b, C a b → D)
    (H₁ : a₁ = a₂)  (H₂ : eq.rec_on H₁ b₁ = b₂) (H₃ : eq.rec_on (congr_arg2_dep C H₁ H₂) c₁ = c₂) :
  f a₁ b₁ c₁ = f a₂ b₂ c₂ :=
eq.rec_on H₁
  (λ (b₂ : B a₁) (H₂ : b₁ = b₂) (c₂ : C a₁ b₂) (H₃ : _ = c₂),
    have H₃' : eq.rec_on H₂ c₁ = c₂,
      from (rec_on_irrel H₂ (congr_arg2_dep C (refl a₁) H₂) c₁⁻¹) ▸ H₃,
    congr_arg2_dep (f a₁) H₂ H₃')
  b₂ H₂ c₂ H₃

theorem congr_arg3_ndep_dep {A B : Type} {C : A → B → Type} {D : Type} {a₁ a₂ : A} {b₁ b₂ : B} {c₁ : C a₁ b₁} {c₂ : C a₂ b₂} (f : Πa b, C a b → D)
    (H₁ : a₁ = a₂)  (H₂ : b₁ = b₂) (H₃ : eq.rec_on (congr_arg2 C H₁ H₂) c₁ = c₂) :
  f a₁ b₁ c₁ = f a₂ b₂ c₂ :=
congr_arg3_dep f H₁ (rec_on_constant H₁ b₁ ⬝ H₂) H₃

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
