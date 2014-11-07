-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Leonardo de Moura, Jeremy Avigad, Floris van Doorn
import general_notation logic.prop data.unit.decl

-- logic.eq
-- ====================

-- Equality.

-- eq
-- --

inductive eq {A : Type} (a : A) : A → Prop :=
refl : eq a a

notation a = b := eq a b
definition rfl {A : Type} {a : A} := eq.refl a

-- proof irrelevance is built in
theorem proof_irrel {a : Prop} (H₁ H₂ : a) : H₁ = H₂ :=
rfl

namespace eq
  variables {A : Type}
  variables {a b c : A}
  theorem id_refl (H₁ : a = a) : H₁ = (eq.refl a) :=
  rfl

  theorem irrel (H₁ H₂ : a = b) : H₁ = H₂ :=
  !proof_irrel

  theorem subst {P : A → Prop} (H₁ : a = b) (H₂ : P a) : P b :=
  rec H₂ H₁

  theorem trans (H₁ : a = b) (H₂ : b = c) : a = c :=
  subst H₂ H₁

  theorem symm (H : a = b) : b = a :=
  subst H (refl a)

  namespace ops
    notation H `⁻¹` := symm H
    notation H1 ⬝ H2 := trans H1 H2
    notation H1 ▸ H2 := subst H1 H2
 end ops
end eq

calc_subst eq.subst
calc_refl  eq.refl
calc_trans eq.trans
calc_symm  eq.symm

open eq.ops

namespace eq
  variables {A B : Type} {a a' a₁ a₂ a₃ a₄ : A}
  definition drec_on {B : Πa' : A, a = a' → Type} (H₁ : a = a') (H₂ : B a (refl a)) : B a' H₁ :=
  eq.rec (λH₁ : a = a, show B a H₁, from H₂) H₁ H₁

--can we remove the theorems about drec_on and only have the rec_on versions?
  -- theorem drec_on_id {B : Πa' : A, a = a' → Type} (H : a = a) (b : B a H) : drec_on H b = b :=
  -- rfl

  -- theorem drec_on_constant (H : a = a') {B : Type} (b : B) : drec_on H b = b :=
  -- drec_on H rfl

  -- theorem drec_on_constant2 (H₁ : a₁ = a₂) (H₂ : a₃ = a₄) (b : B) : drec_on H₁ b = drec_on H₂ b :=
  -- drec_on_constant H₁ b ⬝ (drec_on_constant H₂ b)⁻¹

  
  -- theorem drec_on_irrel_arg {f : A → B} {D : B → Type} (H : a = a') (H' : f a = f a') 
  --     (b : D (f a)) : drec_on H b = drec_on H' b :=
  -- drec_on H (λ(H' : f a = f a), !drec_on_id⁻¹) H'

  -- theorem drec_on_irrel {D : A → Type} (H H' : a = a') (b : D a) : 
  --     drec_on H b = drec_on H' b :=
  -- !drec_on_irrel_arg

  -- theorem drec_on_compose {a b c : A} {P : A → Type} (H₁ : a = b) (H₂ : b = c)
  --         (u : P a) : drec_on H₂ (drec_on H₁ u) = drec_on (trans H₁ H₂) u :=
  --   (show ∀ H₂ : b = c, drec_on H₂ (drec_on H₁ u) = drec_on (trans H₁ H₂) u,
  --     from drec_on H₂ (take (H₂ : b = b), drec_on_id H₂ _))
  --   H₂

  theorem rec_on_id {B : A → Type} (H : a = a) (b : B a) : rec_on H b = b :=
  rfl

  theorem rec_on_constant (H : a = a') {B : Type} (b : B) : rec_on H b = b :=
  drec_on H rfl

  theorem rec_on_constant2 (H₁ : a₁ = a₂) (H₂ : a₃ = a₄) (b : B) : rec_on H₁ b = rec_on H₂ b :=
  rec_on_constant H₁ b ⬝ rec_on_constant H₂ b⁻¹

  theorem rec_on_irrel_arg {f : A → B} {D : B → Type} (H : a = a') (H' : f a = f a') (b : D (f a)) :
                       rec_on H b = rec_on H' b :=
  drec_on H (λ(H' : f a = f a), !rec_on_id⁻¹) H'

  theorem rec_on_irrel {a a' : A} {D : A → Type} (H H' : a = a') (b : D a) : 
      drec_on H b = drec_on H' b :=
  !rec_on_irrel_arg

  --do we need the following?
  -- theorem rec_on_irrel_fun {B : A → Type} {a : A} {f f' : Π x, B x} {D : Π a, B a → Type} (H : f = f') (H' : f a = f' a) (b : D a (f a)) :
  --                      rec_on H b = rec_on H' b :=
  -- sorry

  -- the
  -- theorem rec_on_comm_ap {B : A → Type} {C : Πa, B a → Type} {a a' : A} {f : Π x, C a x} 
  --   (H : a = a') (H' : a = a') (b : B a) : rec_on H f b = rec_on H' (f b) :=
  -- sorry

  theorem rec_on_compose {a b c : A} {P : A → Type} (H₁ : a = b) (H₂ : b = c)
          (u : P a) : rec_on H₂ (rec_on H₁ u) = rec_on (trans H₁ H₂) u :=
    (show ∀ H₂ : b = c, rec_on H₂ (rec_on H₁ u) = rec_on (trans H₁ H₂) u,
      from drec_on H₂ (take (H₂ : b = b), rec_on_id H₂ _))
    H₂
end eq

open eq

section
  variables {A B C D E F : Type}
  variables {a a' : A} {b b' : B} {c c' : C} {d d' : D} {e e' : E}

  theorem congr_fun {B : A → Type} {f g : Π x, B x} (H : f = g) (a : A) : f a = g a :=
  H ▸ rfl

  theorem congr_arg (f : A → B) (H : a = a') : f a = f a' :=
  H ▸ rfl

  theorem congr {f g : A → B} (H₁ : f = g) (H₂ : a = a') : f a = g a' :=
  H₁ ▸ H₂ ▸ rfl

  theorem congr_arg2 (f : A → B → C) (Ha : a = a') (Hb : b = b') : f a b = f a' b' :=
  congr (congr_arg f Ha) Hb

  theorem congr_arg3 (f : A → B → C → D) (Ha : a = a') (Hb : b = b') (Hc : c = c') 
      : f a b c = f a' b' c' :=
  congr (congr_arg2 f Ha Hb) Hc

  theorem congr_arg4 (f : A → B → C → D → E) (Ha : a = a') (Hb : b = b') (Hc : c = c') (Hd : d = d')
      : f a b c d = f a' b' c' d' :=
  congr (congr_arg3 f Ha Hb Hc) Hd

  theorem congr_arg5 (f : A → B → C → D → E → F) 
      (Ha : a = a') (Hb : b = b') (Hc : c = c') (Hd : d = d') (He : e = e') 
        : f a b c d e = f a' b' c' d' e' :=
  congr (congr_arg4 f Ha Hb Hc Hd) He

  theorem congr2 (f f' : A → B → C) (Hf : f = f') (Ha : a = a') (Hb : b = b') : f a b = f' a' b' :=
  Hf ▸ congr_arg2 f Ha Hb

  theorem congr3 (f f' : A → B → C → D) (Hf : f = f') (Ha : a = a') (Hb : b = b') (Hc : c = c') 
      : f a b c = f' a' b' c' :=
  Hf ▸ congr_arg3 f Ha Hb Hc

  theorem congr4 (f f' : A → B → C → D → E) 
      (Hf : f = f') (Ha : a = a') (Hb : b = b') (Hc : c = c') (Hd : d = d')
        : f a b c d = f' a' b' c' d' :=
  Hf ▸ congr_arg4 f Ha Hb Hc Hd

  theorem congr5 (f f' : A → B → C → D → E → F) 
      (Hf : f = f') (Ha : a = a') (Hb : b = b') (Hc : c = c') (Hd : d = d') (He : e = e')
        : f a b c d e = f' a' b' c' d' e' :=
  Hf ▸ congr_arg5 f Ha Hb Hc Hd He
end

theorem equal_f {A : Type} {B : A → Type} {f g : Π x, B x} (H : f = g) : ∀x, f x = g x :=
take x, congr_fun H x

section
  variables {a b c : Prop}

  theorem eqmp (H₁ : a = b) (H₂ : a) : b :=
  H₁ ▸ H₂

  theorem eqmpr (H₁ : a = b) (H₂ : b) : a :=
  H₁⁻¹ ▸ H₂

  theorem eq_true_elim (H : a = true) : a :=
  H⁻¹ ▸ trivial

  theorem eq_false_elim (H : a = false) : ¬a :=
  assume Ha : a, H ▸ Ha

  theorem imp_trans (H₁ : a → b) (H₂ : b → c) : a → c :=
  assume Ha, H₂ (H₁ Ha)

  theorem imp_eq_trans (H₁ : a → b) (H₂ : b = c) : a → c :=
  assume Ha, H₂ ▸ (H₁ Ha)

  theorem eq_imp_trans (H₁ : a = b) (H₂ : b → c) : a → c :=
  assume Ha, H₂ (H₁ ▸ Ha)
end

-- ne
-- --

definition ne {A : Type} (a b : A) := ¬(a = b)
notation a ≠ b := ne a b

namespace ne
  variable {A : Type}
  variables {a b : A}

  theorem intro : (a = b → false) → a ≠ b :=
  assume H, H

  theorem elim : a ≠ b → a = b → false :=
  assume H₁ H₂, H₁ H₂

  theorem irrefl : a ≠ a → false :=
  assume H, H rfl

  theorem symm : a ≠ b → b ≠ a :=
  assume (H : a ≠ b) (H₁ : b = a), H (H₁⁻¹)
end ne

section
  variables {A : Type} {a b c : A}

  theorem a_neq_a_elim : a ≠ a → false :=
  assume H, H rfl

  theorem eq_ne_trans : a = b → b ≠ c → a ≠ c :=
  assume H₁ H₂, H₁⁻¹ ▸ H₂

  theorem ne_eq_trans : a ≠ b → b = c → a ≠ c :=
  assume H₁ H₂, H₂ ▸ H₁
end

calc_trans eq_ne_trans
calc_trans ne_eq_trans

section
  variables {p : Prop}

  theorem p_ne_false : p → p ≠ false :=
  assume (Hp : p) (Heq : p = false), Heq ▸ Hp

  theorem p_ne_true : ¬p → p ≠ true :=
  assume (Hnp : ¬p) (Heq : p = true), absurd trivial (Heq ▸ Hnp)
end

theorem true_ne_false : ¬true = false :=
assume H : true = false,
  H ▸ trivial

inductive subsingleton [class] (A : Type) : Prop :=
intro : (∀ a b : A, a = b) -> subsingleton A

namespace subsingleton
definition elim {A : Type} {H : subsingleton A} : ∀(a b : A), a = b := rec (fun p, p) H
end subsingleton

protected definition prop.subsingleton [instance] (P : Prop) : subsingleton P :=
subsingleton.intro (λa b, !proof_irrel)
