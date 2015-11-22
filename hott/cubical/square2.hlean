/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Coherence conditions for operations on squares
-/

import .square

open equiv

namespace eq

  variables {A B C : Type} {a a' a'' a₀₀ a₂₀ a₄₀ a₀₂ a₂₂ a₂₄ a₀₄ a₄₂ a₄₄ a₁ a₂ a₃ a₄ : A}
            {f : A → B} {b : B} {c : C}
            /-a₀₀-/ {p₁₀ p₁₀' : a₀₀ = a₂₀} /-a₂₀-/ {p₃₀ : a₂₀ = a₄₀} /-a₄₀-/
       {p₀₁ p₀₁' : a₀₀ = a₀₂} /-s₁₁-/ {p₂₁ p₂₁' : a₂₀ = a₂₂} /-s₃₁-/ {p₄₁ : a₄₀ = a₄₂}
            /-a₀₂-/ {p₁₂ p₁₂' : a₀₂ = a₂₂} /-a₂₂-/ {p₃₂ : a₂₂ = a₄₂} /-a₄₂-/
       {p₀₃ : a₀₂ = a₀₄} /-s₁₃-/ {p₂₃ : a₂₂ = a₂₄} /-s₃₃-/ {p₄₃ : a₄₂ = a₄₄}
            /-a₀₄-/ {p₁₄ : a₀₄ = a₂₄} /-a₂₄-/ {p₃₄ : a₂₄ = a₄₄} /-a₄₄-/

  theorem whisker_bl_whisker_tl_eq (p : a = a')
    : whisker_bl p (whisker_tl p ids) = con.right_inv p ⬝ph vrfl :=
  by induction p; reflexivity

  theorem ap_is_constant_natural_square {g : B → C} {f : A → B} (H : Πa, g (f a) = c) (p : a = a') :
    (ap_is_constant H p)⁻¹ ⬝ph natural_square_tr H p ⬝hp ap_constant p c =
      whisker_bl (H a') (whisker_tl (H a) ids) :=
  begin induction p, esimp, rewrite inv_inv, rewrite whisker_bl_whisker_tl_eq end

  definition inv_ph_eq_of_eq_ph {p : a₀₀ = a₀₂} {r : p₀₁ = p} {s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁}
    {s₁₁' : square p₁₀ p₁₂ p p₂₁} (t : s₁₁ = r ⬝ph s₁₁') : r⁻¹ ⬝ph s₁₁ = s₁₁' :=
  by induction r; exact t

  -- the following is used for torus.elim_surf
  theorem whisker_square_aps_eq
    {q₁₀ : f a₀₀ = f a₂₀} {q₀₁ : f a₀₀ = f a₀₂} {q₂₁ : f a₂₀ = f a₂₂} {q₁₂ : f a₀₂ = f a₂₂}
    {r₁₀ : ap f p₁₀ = q₁₀} {r₀₁ : ap f p₀₁ = q₀₁} {r₂₁ : ap f p₂₁ = q₂₁} {r₁₂ : ap f p₁₂ = q₁₂}
    {s₁₁ : p₁₀ ⬝ p₂₁ = p₀₁ ⬝ p₁₂} {t₁₁ : square q₁₀ q₁₂ q₀₁ q₂₁}
    (u : square (ap02 f s₁₁) (eq_of_square t₁₁)
                (ap_con f p₁₀ p₂₁ ⬝ (r₁₀ ◾ r₂₁)) (ap_con f p₀₁ p₁₂ ⬝ (r₀₁ ◾ r₁₂)))
    : whisker_square r₁₀ r₁₂ r₀₁ r₂₁ (aps f (square_of_eq s₁₁)) = t₁₁ :=
  begin
    induction r₁₀, induction r₀₁, induction r₁₂, induction r₂₁,
    induction p₁₂, induction p₁₀, induction p₂₁, esimp at *, induction s₁₁, esimp at *,
    esimp [square_of_eq],
    apply eq_of_fn_eq_fn !square_equiv_eq, esimp,
    exact (eq_bot_of_square u)⁻¹
  end

end eq
