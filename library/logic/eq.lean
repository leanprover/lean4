-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Leonardo de Moura, Jeremy Avigad, Floris van Doorn
import .prop

-- logic.eq
-- ====================

-- Equality.

-- eq
-- --

inductive eq {A : Type} (a : A) : A → Prop :=
refl : eq a a

infix `=` := eq
definition rfl {A : Type} {a : A} := eq.refl a

-- proof irrelevance is built in
theorem proof_irrel {a : Prop} (H₁ H₂ : a) : H₁ = H₂ :=
rfl

namespace eq
section
  variables {A : Type}
  variables {a b c : A}
  theorem id_refl (H₁ : a = a) : H₁ = (eq.refl a) :=
  !proof_irrel

  theorem irrel (H₁ H₂ : a = b) : H₁ = H₂ :=
  !proof_irrel

  theorem subst {P : A → Prop} (H₁ : a = b) (H₂ : P a) : P b :=
  rec H₂ H₁

  theorem trans (H₁ : a = b) (H₂ : b = c) : a = c :=
  subst H₂ H₁

  theorem symm (H : a = b) : b = a :=
  subst H (refl a)
end
namespace ops
  postfix `⁻¹` := symm
  infixr `⬝`   := trans
  infixr `▸`   := subst
end ops
end eq

calc_subst eq.subst
calc_refl  eq.refl
calc_trans eq.trans

open eq.ops

namespace eq
  definition rec_on {A : Type} {a a' : A} {B : Πa' : A, a = a' → Type} (H₁ : a = a') (H₂ : B a (refl a)) : B a' H₁ :=
  eq.rec (λH₁ : a = a, show B a H₁, from H₂) H₁ H₁

  theorem rec_on_id {A : Type} {a : A} {B : Πa' : A, a = a' → Type} (H : a = a) (b : B a H) : rec_on H b = b :=
  refl (rec_on rfl b)

  theorem rec_on_constant {A : Type} {a a' : A} {B : Type} (H : a = a') (b : B) : rec_on H b = b :=
  rec_on H (λ(H' : a = a), rec_on_id H' b) H

  theorem rec_on_constant2 {A : Type} {a₁ a₂ a₃ a₄ : A} {B : Type} (H₁ : a₁ = a₂) (H₂ : a₃ = a₄) (b : B) :
                           rec_on H₁ b = rec_on H₂ b :=
  rec_on_constant H₁ b ⬝ (rec_on_constant H₂ b)⁻¹

  theorem rec_on_irrel {A B : Type} {a a' : A} {f : A → B} {D : B → Type} (H : a = a') (H' : f a = f a') (b : D (f a)) :
                       rec_on H b = rec_on H' b :=
  rec_on H (λ(H : a = a) (H' : f a = f a), rec_on_id H b ⬝ rec_on_id H' b⁻¹) H H'

  theorem rec_id {A : Type} {a : A} {B : A → Type} (H : a = a) (b : B a) : rec b H = b :=
  id_refl H⁻¹ ▸ refl (eq.rec b (refl a))

  theorem rec_on_compose {A : Type} {a b c : A} {P : A → Type} (H₁ : a = b) (H₂ : b = c)
          (u : P a) :
    rec_on H₂ (rec_on H₁ u) = rec_on (trans H₁ H₂) u :=
    (show ∀ H₂ : b = c, rec_on H₂ (rec_on H₁ u) = rec_on (trans H₁ H₂) u,
      from rec_on H₂ (take (H₂ : b = b), rec_on_id H₂ _))
    H₂
end eq

open eq

section
  variables {A B C D E F : Type}
  variables {a a' : A} {b b' : B} {c c' : C} {d d' : D} {e e' : E} {f f' : F}

  theorem congr_fun {B : A → Type} {f g : Π x, B x} (H : f = g) (a : A) : f a = g a :=
  H ▸ rfl

  theorem congr_arg (f : A → B) (H : a = a') : f a = f a' :=
  H ▸ rfl

  theorem congr {f g : A → B} (H₁ : f = g) (H₂ : a = a') : f a = g a' :=
  H₁ ▸ H₂ ▸ rfl

  theorem congr_arg2 (f : A → B → C) (Ha : a = a') (Hb : b = b') : f a b = f a' b' :=
  congr (congr_arg f Ha) Hb

  theorem congr_arg3 (f : A → B → C → D) (Ha : a = a') (Hb : b = b') (Hc : c = c') : f a b c = f a' b' c' :=
  congr (congr_arg2 f Ha Hb) Hc

  theorem congr_arg4 (f : A → B → C → D → E) (Ha : a = a') (Hb : b = b') (Hc : c = c') (Hd : d = d') : f a b c d = f a' b' c' d' :=
  congr (congr_arg3 f Ha Hb Hc) Hd

  theorem congr_arg5 (f : A → B → C → D → E → F) (Ha : a = a') (Hb : b = b') (Hc : c = c') (Hd : d = d') (He : e = e')
                     : f a b c d e = f a' b' c' d' e' :=
  congr (congr_arg4 f Ha Hb Hc Hd) He

  theorem congr2 (f f' : A → B → C) (Hf : f = f') (Ha : a = a') (Hb : b = b') : f a b = f' a' b' :=
  Hf ▸ congr_arg2 f Ha Hb

  theorem congr3 (f f' : A → B → C → D) (Hf : f = f') (Ha : a = a') (Hb : b = b') (Hc : c = c') : f a b c = f' a' b' c' :=
  Hf ▸ congr_arg3 f Ha Hb Hc

  theorem congr4 (f f' : A → B → C → D → E) (Hf : f = f') (Ha : a = a') (Hb : b = b') (Hc : c = c') (Hd : d = d')
                 : f a b c d = f' a' b' c' d' :=
  Hf ▸ congr_arg4 f Ha Hb Hc Hd

  theorem congr5 (f f' : A → B → C → D → E → F) (Hf : f = f') (Ha : a = a') (Hb : b = b') (Hc : c = c') (Hd : d = d') (He : e = e')
                 : f a b c d e = f' a' b' c' d' e' :=
  Hf ▸ congr_arg5 f Ha Hb Hc Hd He
end

section
  variables {A : Type} {B : A → Type} {C : Πa, B a → Type} {D : Πa b, C a b → Type} {R : Type}
  variables {a₁ a₂ : A} 
            {b₁ : B a₁} {b₂ : B a₂} 
            {c₁ : C a₁ b₁} {c₂ : C a₂ b₂} 
            {d₁ : D a₁ b₁ c₁} {d₂ : D a₂ b₂ c₂}

  theorem congr_arg2_dep (f : Πa, B a → R) (H₁ : a₁ = a₂) (H₂ : eq.rec_on H₁ b₁ = b₂) 
      : f a₁ b₁ = f a₂ b₂ :=
  eq.rec_on H₁
    (λ (b₂ : B a₁) (H₁ : a₁ = a₁) (H₂ : eq.rec_on H₁ b₁ = b₂),
      calc
        f a₁ b₁ = f a₁ (eq.rec_on H₁ b₁) : {(eq.rec_on_id H₁ b₁)⁻¹}
            ... = f a₁ b₂                : {H₂})
    b₂ H₁ H₂

  theorem congr_arg3_dep (f : Πa b, C a b → R) (H₁ : a₁ = a₂) (H₂ : eq.rec_on H₁ b₁ = b₂)
      (H₃ : eq.rec_on (congr_arg2_dep C H₁ H₂) c₁ = c₂) : f a₁ b₁ c₁ = f a₂ b₂ c₂ :=
  eq.rec_on H₁
    (λ (b₂ : B a₁) (H₂ : b₁ = b₂) (c₂ : C a₁ b₂)
      (H₃ : (rec_on (congr_arg2_dep C (refl a₁) H₂) c₁) = c₂),
      have H₃' : eq.rec_on H₂ c₁ = c₂, from rec_on_irrel H₂ _ c₁ ⬝ H₃,
      congr_arg2_dep (f a₁) H₂ H₃')
    b₂ H₂ c₂ H₃

  -- for the moment the following theorem is commented out, because it takes long to prove
  -- theorem congr_arg4_dep (f : Πa b c, D a b c → R) (H₁ : a₁ = a₂) (H₂ : eq.rec_on H₁ b₁ = b₂)
  --     (H₃ : eq.rec_on (congr_arg2_dep C H₁ H₂) c₁ = c₂) 
  --     (H₄ : eq.rec_on (congr_arg3_dep D H₁ H₂ H₃) d₁ = d₂) : f a₁ b₁ c₁ d₁ = f a₂ b₂ c₂ d₂ :=
  -- eq.rec_on H₁
  --   (λ b₂ H₂ c₂ H₃ d₂ (H₄ : _),
  --     have H₃' [visible] : eq.rec_on H₂ c₁ = c₂, from rec_on_irrel H₂ _ c₁ ⬝ H₃,
  --     have H₄' : rec_on (congr_arg2_dep (D a₁) H₂ H₃') d₁ = d₂, from rec_on_irrel _ _ d₁ ⬝ H₄,
  --     congr_arg3_dep (f a₁) H₂ H₃' H₄')
  --   b₂ H₂ c₂ H₃ d₂ H₄
end

section
  variables {A B : Type} {C : A → B → Type} {R : Type}
  variables {a₁ a₂ : A} {b₁ b₂ : B} {c₁ : C a₁ b₁} {c₂ : C a₂ b₂}
  theorem congr_arg3_ndep_dep (f : Πa b, C a b → R) (H₁ : a₁ = a₂) (H₂ : b₁ = b₂) (H₃ : eq.rec_on (congr_arg2 C H₁ H₂) c₁ = c₂) :
                              f a₁ b₁ c₁ = f a₂ b₂ c₂ :=
  congr_arg3_dep f H₁ (rec_on_constant H₁ b₁ ⬝ H₂) H₃
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
infix `≠` := ne

namespace ne
section
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
end
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
definition elim {A : Type} (H : subsingleton A) : ∀(a b : A), a = b :=
rec (fun p, p) H
end subsingleton

protected definition prop.subsingleton [instance] (P : Prop) : subsingleton P := 
subsingleton.intro (λa b, !proof_irrel)
