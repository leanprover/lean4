/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Floris van Doorn

Additional declarations/theorems about equality. See also init.datatypes and init.logic.
-/

open eq.ops

namespace eq
  variables {A B : Type} {a a' a₁ a₂ a₃ a₄ : A}

  theorem irrel (H₁ H₂ : a = a') : H₁ = H₂ :=
  !proof_irrel

  theorem id_refl (H₁ : a = a) : H₁ = (eq.refl a) :=
  rfl

  theorem rec_on_id {B : A → Type} (H : a = a) (b : B a) : eq.rec_on H b = b :=
  rfl

  theorem rec_on_constant (H : a = a') {B : Type} (b : B) : eq.rec_on H b = b :=
  eq.drec_on H rfl

  theorem rec_on_constant2 (H₁ : a₁ = a₂) (H₂ : a₃ = a₄) (b : B) : eq.rec_on H₁ b = eq.rec_on H₂ b :=
  rec_on_constant H₁ b ⬝ (rec_on_constant H₂ b)⁻¹

  theorem rec_on_irrel_arg {f : A → B} {D : B → Type} (H : a = a') (H' : f a = f a') (b : D (f a)) :
                       eq.rec_on H b = eq.rec_on H' b :=
  eq.drec_on H (λ(H' : f a = f a), !rec_on_id⁻¹) H'

  theorem rec_on_irrel {a a' : A} {D : A → Type} (H H' : a = a') (b : D a) :
      eq.drec_on H b = eq.drec_on H' b :=
  proof_irrel H H' ▸ rfl

  theorem rec_on_compose {a b c : A} {P : A → Type} (H₁ : a = b) (H₂ : b = c)
          (u : P a) : eq.rec_on H₂ (eq.rec_on H₁ u) = eq.rec_on (trans H₁ H₂) u :=
    (show ∀ H₂ : b = c, eq.rec_on H₂ (eq.rec_on H₁ u) = eq.rec_on (trans H₁ H₂) u,
      from eq.drec_on H₂ (take (H₂ : b = b), rec_on_id H₂ _))
    H₂
end eq

open eq

section
  variables {A B C D E F : Type}
  variables {a a' : A} {b b' : B} {c c' : C} {d d' : D} {e e' : E}

  theorem congr_arg2 (f : A → B → C) (Ha : a = a') (Hb : b = b') : f a b = f a' b' :=
  by substvars

  theorem congr_arg3 (f : A → B → C → D) (Ha : a = a') (Hb : b = b') (Hc : c = c')
      : f a b c = f a' b' c' :=
  by substvars

  theorem congr_arg4 (f : A → B → C → D → E) (Ha : a = a') (Hb : b = b') (Hc : c = c') (Hd : d = d')
      : f a b c d = f a' b' c' d' :=
  by substvars

  theorem congr_arg5 (f : A → B → C → D → E → F)
      (Ha : a = a') (Hb : b = b') (Hc : c = c') (Hd : d = d') (He : e = e')
        : f a b c d e = f a' b' c' d' e' :=
  by substvars

  theorem congr2 (f f' : A → B → C) (Hf : f = f') (Ha : a = a') (Hb : b = b') : f a b = f' a' b' :=
  by substvars

  theorem congr3 (f f' : A → B → C → D) (Hf : f = f') (Ha : a = a') (Hb : b = b') (Hc : c = c')
      : f a b c = f' a' b' c' :=
  by substvars

  theorem congr4 (f f' : A → B → C → D → E)
      (Hf : f = f') (Ha : a = a') (Hb : b = b') (Hc : c = c') (Hd : d = d')
        : f a b c d = f' a' b' c' d' :=
  by substvars

  theorem congr5 (f f' : A → B → C → D → E → F)
      (Hf : f = f') (Ha : a = a') (Hb : b = b') (Hc : c = c') (Hd : d = d') (He : e = e')
        : f a b c d e = f' a' b' c' d' e' :=
  by substvars
end

theorem equal_f {A : Type} {B : A → Type} {f g : Π x, B x} (H : f = g) : ∀x, f x = g x :=
take x, congr_fun H x

section
  variables {a b c : Prop}

  theorem eqmp (H₁ : a = b) (H₂ : a) : b :=
  H₁ ▸ H₂

  theorem eqmpr (H₁ : a = b) (H₂ : b) : a :=
  H₁⁻¹ ▸ H₂

  theorem imp_trans (H₁ : a → b) (H₂ : b → c) : a → c :=
  assume Ha, H₂ (H₁ Ha)

  theorem imp_eq_trans (H₁ : a → b) (H₂ : b = c) : a → c :=
  assume Ha, H₂ ▸ (H₁ Ha)

  theorem eq_imp_trans (H₁ : a = b) (H₂ : b → c) : a → c :=
  assume Ha, H₂ (H₁ ▸ Ha)
end

section
  variables {p : Prop}

  theorem p_ne_false : p → p ≠ false :=
  assume (Hp : p) (Heq : p = false), Heq ▸ Hp

  theorem p_ne_true : ¬p → p ≠ true :=
  assume (Hnp : ¬p) (Heq : p = true), (Heq ▸ Hnp) trivial
end

theorem true_ne_false : ¬true = false :=
p_ne_false trivial
