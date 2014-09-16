-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura, Jeremy Avigad
import logic.core.inhabited logic.core.eq
open inhabited eq_ops

inductive sigma {A : Type} (B : A → Type) : Type :=
dpair : Πx : A, B x → sigma B

notation `Σ` binders `,` r:(scoped P, sigma P) := r

namespace sigma
section
  parameters {A : Type} {B : A → Type}

  abbreviation dpr1 (p : Σ x, B x) : A := rec (λ a b, a) p
  abbreviation dpr2 (p : Σ x, B x) : B (dpr1 p) := rec (λ a b, b) p

  theorem dpr1_dpair (a : A) (b : B a) : dpr1 (dpair a b) = a := rfl
  theorem dpr2_dpair (a : A) (b : B a) : dpr2 (dpair a b) = b := rfl

  theorem destruct [protected] {P : sigma B → Prop} (p : sigma B) (H : ∀a b, P (dpair a b)) : P p :=
  rec H p

  theorem dpair_ext (p : sigma B) : dpair (dpr1 p) (dpr2 p) = p :=
  destruct p (take a b, rfl)

  theorem dpair_eq {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂} (H₁ : a₁ = a₂) (H₂ : eq.rec_on H₁ b₁ = b₂) :
    dpair a₁ b₁ = dpair a₂ b₂ :=
  eq.rec_on H₁
    (λ (b₂ : B a₁) (H₁ : a₁ = a₁) (H₂ : eq.rec_on H₁ b₁ = b₂),
      calc
        dpair a₁ b₁ = dpair a₁ (eq.rec_on H₁ b₁) : {(eq.rec_on_id H₁ b₁)⁻¹}
                ... = dpair a₁ b₂                : {H₂})
    b₂ H₁ H₂

  theorem equal [protected] {p₁ p₂ : Σx : A, B x} :
    ∀(H₁ : dpr1 p₁ = dpr1 p₂) (H₂ : eq.rec_on H₁ (dpr2 p₁) = (dpr2 p₂)), p₁ = p₂ :=
  destruct p₁ (take a₁ b₁, destruct p₂ (take a₂ b₂ H₁ H₂, dpair_eq H₁ H₂))

  theorem is_inhabited [protected] [instance] (H₁ : inhabited A) (H₂ : inhabited (B (default A))) :
    inhabited (sigma B) :=
  inhabited.destruct H₁ (λa, inhabited.destruct H₂ (λb, inhabited.mk (dpair (default A) b)))
end
end sigma
