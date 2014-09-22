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

  definition dpr1 (p : Σ x, B x) : A := rec (λ a b, a) p
  definition dpr2 (p : Σ x, B x) : B (dpr1 p) := rec (λ a b, b) p

  theorem dpr1_dpair (a : A) (b : B a) : dpr1 (dpair a b) = a := rfl
  theorem dpr2_dpair (a : A) (b : B a) : dpr2 (dpair a b) = b := rfl

  protected theorem destruct {P : sigma B → Prop} (p : sigma B) (H : ∀a b, P (dpair a b)) : P p :=
  rec H p

  theorem dpair_ext (p : sigma B) : dpair (dpr1 p) (dpr2 p) = p :=
  destruct p (take a b, rfl)

  theorem dpair_eq {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂} (H₁ : a₁ = a₂) (H₂ : eq.rec_on H₁ b₁ = b₂) :
    dpair a₁ b₁ = dpair a₂ b₂ :=
  congr_arg2 dpair H₁ H₂

  protected theorem equal {p₁ p₂ : Σx : A, B x} :
    ∀(H₁ : dpr1 p₁ = dpr1 p₂) (H₂ : eq.rec_on H₁ (dpr2 p₁) = dpr2 p₂), p₁ = p₂ :=
  destruct p₁ (take a₁ b₁, destruct p₂ (take a₂ b₂ H₁ H₂, dpair_eq H₁ H₂))

  protected theorem is_inhabited [instance] (H₁ : inhabited A) (H₂ : inhabited (B (default A))) :
    inhabited (sigma B) :=
  inhabited.destruct H₁ (λa, inhabited.destruct H₂ (λb, inhabited.mk (dpair (default A) b)))
end

section trip_quad
  parameters {A : Type} {B : A → Type} {C : Πa, B a → Type} {D : Πa b, C a b → Type}

  definition dtrip (a : A) (b : B a) (c : C a b) := dpair a (dpair b c)
  definition dquad (a : A) (b : B a) (c : C a b) (d : D a b c) := dpair a (dpair b (dpair c d))

  definition dpr1' (x : Σ a, B a) := dpr1 x
  definition dpr2' (x : Σ a b, C a b) := dpr1 (dpr2 x)
  definition dpr3  (x : Σ a b, C a b) := dpr2 (dpr2 x)
  definition dpr3' (x : Σ a b c, D a b c) := dpr1 (dpr2 (dpr2 x))
  definition dpr4  (x : Σ a b c, D a b c) := dpr2 (dpr2 (dpr2 x))

  -- theorem dtrip_eq {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂} {c₁ : C a₁ b₁} {c₂ : C a₂ b₂}
  --     (H₁ : a₁ = a₂)  (H₂ : eq.rec_on H₁ b₁ = b₂) (H₃ : eq.rec_on (congr_arg2 C H₁ H₂) c₁ = c₂) :
  --   dtrip a₁ b₁ c₁ = dtrip a₂ b₂ c₂ :=
  -- eq.rec_on H₁
  --   (λ (b₂ : B a₁) (c₂ : C a₁ b₂) (H₁ : a₁ = a₁) (H₂ : eq.rec_on H₁ b₁ = b₂)
  --       (x : (eq (eq.rec_on (congr_arg2 C H₁ H₂) c₁) c₂)), sorry
  --     -- have H : dpair b₁ c₁ = dpair b₂ c₂, from
  --     --   dpair_eq H₂ (eq.subst (eq.rec_on_id H₁ c₁) H₃),
  --     -- eq.subst H rfl
  --   )
  --   b₂ c₂ H₁ H₂ H₃
end trip_quad

  theorem dtrip_eq2 {A B : Type} {C : A → B → Type} {a₁ a₂ : A} {b₁ b₂ : B}
      {c₁ : C a₁ b₁} {c₂ : C a₂ b₂} (H₁ : a₁ = a₂)  (H₂ : b₁ = b₂)
      (H₃ : eq.rec_on H₂ (eq.rec_on H₁ c₁) = c₂) :
    dtrip a₁ b₁ c₁ = dtrip a₂ b₂ c₂ :=
  eq.rec_on H₁
    (λ (b₂ : B) (c₂ : C a₁ b₂) (H₁ : a₁ = a₁) (H₂ : b₁ = b₂)
        (H₃ : eq.rec_on H₂ (eq.rec_on H₁ c₁) = c₂),
      have H : dpair b₁ c₁ = dpair b₂ c₂, from
        dpair_eq H₂ (eq.subst (eq.rec_on_id H₁ c₁) H₃),
      eq.subst H rfl
    )
    b₂ c₂ H₁ H₂ H₃

  theorem trip.equal2 {A B : Type} {C : A → B → Type} {p₁ p₂ : Σa b, C a b} :
      ∀(H₁ : dpr1 p₁ = dpr1 p₂) (H₂ : dpr2' p₁ = dpr2' p₂)
      (H₃ : eq.rec_on H₂ (eq.rec_on H₁ (dpr3 p₁)) = dpr3 p₂), p₁ = p₂ :=
  destruct p₁ (take a₁ q₁, destruct q₁ (take b₁ c₁, destruct p₂ (take a₂ q₂, destruct q₂
    (take b₂ c₂ H₁ H₂ H₃, dtrip_eq2 H₁ H₂ H₃))))

end sigma
