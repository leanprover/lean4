/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Theorems about pullbacks
-/

import cubical.square
open eq equiv is_equiv function equiv.ops prod unit is_trunc sigma

variables {A₀₀ A₂₀ A₄₀ A₀₂ A₂₂ A₄₂ : Type}
          (f₁₀ : A₀₀ → A₂₀) (f₃₀ : A₂₀ → A₄₀)
          (f₀₁ : A₀₀ → A₀₂) (f₂₁ : A₂₀ → A₂₂) (f₄₁ : A₄₀ → A₄₂)
          (f₁₂ : A₀₂ → A₂₂) (f₃₂ : A₂₂ → A₄₂)

structure pullback (f₂₁ : A₂₀ → A₂₂) (f₁₂ : A₀₂ → A₂₂) :=
  (pr1 : A₂₀)
  (pr2 : A₀₂)
  (pr1_pr2 : f₂₁ pr1 = f₁₂ pr2)

namespace pullback

  protected definition sigma_char [constructor] :
    pullback f₂₁ f₁₂ ≃ Σ(a₂₀ : A₂₀) (a₀₂ : A₀₂), f₂₁ a₂₀ = f₁₂ a₀₂ :=
  begin
    fapply equiv.MK,
    { intro x, induction x with a₂₀ a₀₂ p, exact ⟨a₂₀, a₀₂, p⟩},
    { intro x, induction x with a₂₀ y, induction y with a₀₂ p, exact pullback.mk a₂₀ a₀₂ p},
    { intro x, induction x with a₂₀ y, induction y with a₀₂ p, reflexivity},
    { intro x, induction x with a₂₀ a₀₂ p, reflexivity},
  end

  variables {f₁₀ f₃₀ f₀₁ f₂₁ f₄₁ f₁₂ f₃₂}

  definition pullback_corec [constructor] (p : Πa, f₂₁ (f₁₀ a) = f₁₂ (f₀₁ a)) (a : A₀₀)
    : pullback f₂₁ f₁₂ :=
  pullback.mk (f₁₀ a) (f₀₁ a) (p a)

  definition pullback_eq {x y : pullback f₂₁ f₁₂} (p1 : pr1 x = pr1 y) (p2 : pr2 x = pr2 y)
    (r : square (pr1_pr2 x) (pr1_pr2 y) (ap f₂₁ p1) (ap f₁₂ p2)) : x = y :=
  by induction y; induction x; esimp at *; induction p1; induction p2;
     exact ap (pullback.mk _ _) (eq_of_vdeg_square r)

  definition pullback_comm_equiv [constructor] : pullback f₁₂ f₂₁ ≃ pullback f₂₁ f₁₂ :=
  begin
    fapply equiv.MK,
    { intro v, induction v with x y p, exact pullback.mk y x p⁻¹},
    { intro v, induction v with x y p, exact pullback.mk y x p⁻¹},
    { intro v, induction v, esimp, exact ap _ !inv_inv},
    { intro v, induction v, esimp, exact ap _ !inv_inv},
  end

  definition pullback_unit_equiv [constructor]
    : pullback (λ(x : A₀₂), star) (λ(x : A₂₀), star) ≃ A₀₂ × A₂₀ :=
  begin
    fapply equiv.MK,
    { intro v, induction v with x y p, exact (x, y)},
    { intro v, induction v with x y, exact pullback.mk x y idp},
    { intro v, induction v, reflexivity},
    { intro v, induction v, esimp, apply ap _ !is_hprop.elim},
  end

  definition pullback_along {f : A₂₀ → A₂₂} (g : A₀₂ → A₂₂) : pullback f g → A₂₀ :=
  pr1

  postfix `^*`:(max+1) := pullback_along

  variables (f₁₀ f₃₀ f₀₁ f₂₁ f₄₁ f₁₂ f₃₂)

  structure pullback_square (f₁₀ : A₀₀ → A₂₀) (f₁₂ : A₀₂ → A₂₂) (f₀₁ : A₀₀ → A₀₂) (f₂₁ : A₂₀ → A₂₂)
    : Type :=
    (comm : Πa, f₂₁ (f₁₀ a) = f₁₂ (f₀₁ a))
    (is_pullback : is_equiv (pullback_corec comm : A₀₀ → pullback f₂₁ f₁₂))

  attribute pullback_square.is_pullback [instance]
  definition pbs_comm [unfold 9] := @pullback_square.comm

  definition pullback_square_pullback
    : pullback_square (pr1 : pullback f₂₁ f₁₂ → A₂₀) f₁₂ pr2 f₂₁ :=
  pullback_square.mk
    pr1_pr2
    (adjointify _ (λf, f)
                  (λf, by induction f; reflexivity)
                  (λg, by induction g; reflexivity))

  variables {f₁₀ f₃₀ f₀₁ f₂₁ f₄₁ f₁₂ f₃₂}

  definition pullback_square_equiv [constructor] (s : pullback_square f₁₀ f₁₂ f₀₁ f₂₁)
    : A₀₀ ≃ pullback f₂₁ f₁₂ :=
  equiv.mk _ (pullback_square.is_pullback s)

  definition of_pullback [unfold 9] (s : pullback_square f₁₀ f₁₂ f₀₁ f₂₁)
    (x : pullback f₂₁ f₁₂) : A₀₀ :=
  (pullback_square_equiv s)⁻¹ x

  definition right_of_pullback (s : pullback_square f₁₀ f₁₂ f₀₁ f₂₁)
    (x : pullback f₂₁ f₁₂) : f₁₀ (of_pullback s x) = pr1 x :=
  ap pr1 (to_right_inv (pullback_square_equiv s) x)

  definition down_of_pullback (s : pullback_square f₁₀ f₁₂ f₀₁ f₂₁)
    (x : pullback f₂₁ f₁₂) : f₀₁ (of_pullback s x) = pr2 x :=
  ap pr2 (to_right_inv (pullback_square_equiv s) x)

  -- definition pullback_square_compose_inverse (s : pullback_square f₁₀ f₁₂ f₀₁ f₂₁)
  --   (t : pullback_square f₃₀ f₃₂ f₂₁ f₄₁) (x : pullback f₄₁ (f₃₂ ∘ f₁₂)) : A₀₀ :=
  -- let a₂₀' : pullback f₄₁ f₃₂ :=
  --   pullback.mk (pr1 x) (f₁₂ (pr2 x)) (pr1_pr2 x) in
  -- let a₂₀ : A₂₀ :=
  --   of_pullback t a₂₀' in
  -- have a₀₀' : pullback f₂₁ f₁₂,
  --   from pullback.mk a₂₀ (pr2 x) !down_of_pullback,
  -- show A₀₀,
  --   from of_pullback s a₀₀'
  -- local attribute pullback_square_compose_inverse [reducible]

  -- definition down_psci (s : pullback_square f₁₀ f₁₂ f₀₁ f₂₁)
  --   (t : pullback_square f₃₀ f₃₂ f₂₁ f₄₁) (x : pullback f₄₁ (f₃₂ ∘ f₁₂)) :
  --    f₀₁ (pullback_square_compose_inverse s t x) = pr2 x :=
  -- by apply down_of_pullback

  -- definition pullback_square_compose [constructor] (s : pullback_square f₁₀ f₁₂ f₀₁ f₂₁)
  --   (t : pullback_square f₃₀ f₃₂ f₂₁ f₄₁) : pullback_square (f₃₀ ∘ f₁₀) (f₃₂ ∘ f₁₂) f₀₁ f₄₁ :=
  -- pullback_square.mk
  --   (λa, pbs_comm t (f₁₀ a) ⬝ ap f₃₂ (pbs_comm s a))
  --   (adjointify _
  --     (pullback_square_compose_inverse s t)
  --     begin
  --       intro x, induction x with x y p, esimp,
  --       fapply pullback_eq: esimp,
  --       { exact ap f₃₀ !right_of_pullback ⬝ !right_of_pullback},
  --       { apply down_of_pullback},
  --       { esimp, exact sorry }
  --     end
  --     begin
  --       intro x, esimp, exact sorry
  --     end)

end pullback
